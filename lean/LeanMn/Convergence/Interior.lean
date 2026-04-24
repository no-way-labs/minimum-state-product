import LeanMn.Convergence.TP

namespace LeanMn

open scoped BigOperators

def IsMidHopTriple (L S R : Nat) : Prop :=
  (L = 0 ∧ S = 2 ∧ R = 2) ∨
    (L = 1 ∧ S = 0 ∧ R = 0) ∨
    (L = 1 ∧ S = 1 ∧ R = 2)

def midHopBudgetVal (L S : Nat) : Nat :=
  if L = 0 then
    if S = 2 then 1 else 0
  else if L = 1 then
    2 - S
  else
    0

def midHopBudget (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) : Nat :=
  midHopBudgetVal (c (left i)).1 (c i).1

def cup2MidTpZeroStepAt (n : Nat) (hn : 4 ≤ n) (i : Fin n)
    (c' c : Config (cup2Spec n hn)) : Prop :=
  privileged (cup2System n hn) c i ∧
    c' = move (cup2System n hn) c i ∧
      cup2Fc n hn c' = cup2Fc n hn c ∧
        cup2TpPreservingMove n hn c i

lemma mid_tp_zero_cases (n : Nat) {i : Fin n}
    (h3 : 3 ≤ i.1) (htop : i.1 + 2 < n)
    (L S R : Fin 3)
    (hfc : localFcAfter L.1 S.1 R.1 (TMidVal L.1 S.1 R.1) = localFcBefore L.1 S.1 R.1)
    (hexp2 : localExp2After n i L.1 S.1 R.1 (TMidVal L.1 S.1 R.1) =
      localExp2Before n i L.1 S.1 R.1)
    (hi21 : localInt21After n i L.1 S.1 R.1 (TMidVal L.1 S.1 R.1) =
      localInt21Before n i L.1 S.1 R.1)
    (hweight : localExp2WeightAfter n i L.1 S.1 R.1 (TMidVal L.1 S.1 R.1) =
      localExp2WeightBefore n i L.1 S.1 R.1)
    (hpriv : TMidVal L.1 S.1 R.1 ≠ S.1) :
    IsMidHopTriple L.1 S.1 R.1 := by
  have h0 : i.1 ≠ 0 := by omega
  have h1 : i.1 ≠ 1 := by omega
  have hleftv : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
  have hiin : 2 ≤ i.1 := by omega
  have hleftin' : 2 ≤ i.1 - 1 := by omega
  have hlefttop' : i.1 - 1 + 2 < n := by omega
  unfold localExp2After localExp2Before at hexp2
  unfold localInt21After localInt21Before at hi21
  unfold localExp2WeightAfter localExp2WeightBefore at hweight
  rw [hleftv] at hexp2 hi21 hweight
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [IsMidHopTriple, localFcAfter, localFcBefore, frontierBitVal, TMidVal,
      cup2Exp2BitVal, cup2Int21BitVal,
      hleftin', hlefttop', hiin, htop] at hfc hexp2 hi21 hweight hpriv ⊢ <;> omega

lemma mid_tp_copyNeighbor (n : Nat) {i : Fin n}
    (h3 : 3 ≤ i.1) (htop : i.1 + 2 < n)
    (L S R : Fin 3)
    (hexp2 : localExp2After n i L.1 S.1 R.1 (TMidVal L.1 S.1 R.1) =
      localExp2Before n i L.1 S.1 R.1)
    (hi21 : localInt21After n i L.1 S.1 R.1 (TMidVal L.1 S.1 R.1) =
      localInt21Before n i L.1 S.1 R.1)
    (hweight : localExp2WeightAfter n i L.1 S.1 R.1 (TMidVal L.1 S.1 R.1) =
      localExp2WeightBefore n i L.1 S.1 R.1)
    (hpriv : TMidVal L.1 S.1 R.1 ≠ S.1) :
    TMidVal L.1 S.1 R.1 = L.1 ∨ TMidVal L.1 S.1 R.1 = R.1 := by
  have h0 : i.1 ≠ 0 := by omega
  have h1 : i.1 ≠ 1 := by omega
  have hleftv : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
  have hiin : 2 ≤ i.1 := by omega
  have hleftin' : 2 ≤ i.1 - 1 := by omega
  have hlefttop' : i.1 - 1 + 2 < n := by omega
  unfold localExp2After localExp2Before at hexp2
  unfold localInt21After localInt21Before at hi21
  unfold localExp2WeightAfter localExp2WeightBefore at hweight
  rw [hleftv] at hexp2 hi21 hweight
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [TMidVal, cup2Exp2BitVal, cup2Int21BitVal,
      localExp2WeightAfter, localExp2WeightBefore,
      hleftin', hlefttop', hiin, htop] at hexp2 hi21 hweight hpriv ⊢ <;> omega

theorem cup2TpPreserving_mid_copyNeighbor_val (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i : Fin n)
    (h3 : 3 ≤ i.1) (htop : i.1 + 2 < n)
    (htp : cup2TpPreservingMove n hn c i)
    (hpriv : privileged (cup2System n hn) c i) :
    cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = (c (left i)).1 ∨
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = (c (right i)).1 := by
  have h0 : i.1 ≠ 0 := by omega
  have h1 : i.1 ≠ 1 := by omega
  have htop' : i.1 + 1 ≠ n := by omega
  have hhigh : i.1 + 2 ≠ n := by omega
  have hpriv_val :
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 ≠ (c i).1 := by
    simpa [privileged, cup2System, cup2Trans_val, Fin.ne_iff_vne] using hpriv
  let L : Fin 3 := ⟨(c (left i)).1, by
    simpa [cup2Spec, cup2M_left_mid hn h0 h1 htop'] using (c (left i)).2⟩
  let S : Fin 3 := ⟨(c i).1, by
    simpa [cup2Spec, cup2M_self_mid hn h0 htop'] using (c i).2⟩
  let R : Fin 3 := ⟨(c (right i)).1, by
    simpa [cup2Spec, cup2M_right_mid hn h0 htop' hhigh] using (c (right i)).2⟩
  have hout : cup2OutVal n i L.1 S.1 R.1 = TMidVal L.1 S.1 R.1 := by
    simp [L, S, R, cup2OutVal, h0, h1, htop', hhigh]
  obtain ⟨hexp2, hi21, hweight⟩ := cup2TpPreserving_local_eqs n hn c i htp
  have hexp2' : localExp2After n i L.1 S.1 R.1 (TMidVal L.1 S.1 R.1) =
      localExp2Before n i L.1 S.1 R.1 := by
    simpa [L, S, R, hout] using hexp2
  have hi21' : localInt21After n i L.1 S.1 R.1 (TMidVal L.1 S.1 R.1) =
      localInt21Before n i L.1 S.1 R.1 := by
    simpa [L, S, R, hout] using hi21
  have hweight' : localExp2WeightAfter n i L.1 S.1 R.1 (TMidVal L.1 S.1 R.1) =
      localExp2WeightBefore n i L.1 S.1 R.1 := by
    simpa [L, S, R, hout] using hweight
  have hcopy := mid_tp_copyNeighbor n h3 htop L S R hexp2' hi21' hweight'
    (by simpa [L, S, R, hout] using hpriv_val)
  simpa [L, S, R, hout] using hcopy

theorem cup2TpPreserving_mid_zero_cases_val (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i : Fin n)
    (h3 : 3 ≤ i.1) (htop : i.1 + 2 < n)
    (hfc : cup2Fc n hn (move (cup2System n hn) c i) = cup2Fc n hn c)
    (htp : cup2TpPreservingMove n hn c i)
    (hpriv : privileged (cup2System n hn) c i) :
    IsMidHopTriple (c (left i)).1 (c i).1 (c (right i)).1 := by
  have h0 : i.1 ≠ 0 := by omega
  have h1 : i.1 ≠ 1 := by omega
  have htop' : i.1 + 1 ≠ n := by omega
  have hhigh : i.1 + 2 ≠ n := by omega
  have hpriv_val :
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 ≠ (c i).1 := by
    simpa [privileged, cup2System, cup2Trans_val, Fin.ne_iff_vne] using hpriv
  obtain ⟨hexp2, hi21, hweight⟩ := cup2TpPreserving_local_eqs n hn c i htp
  have hfc_local :
      localFcAfter (c (left i)).1 (c i).1 (c (right i)).1
          (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) =
        localFcBefore (c (left i)).1 (c i).1 (c (right i)).1 := by
    rw [cup2Fc_move_split n hn c i, cup2Fc_split n hn c i, cup2Fc_rest_move_eq n hn c i] at hfc
    omega
  let L : Fin 3 := ⟨(c (left i)).1, by
    simpa [cup2Spec, cup2M_left_mid hn h0 h1 htop'] using (c (left i)).2⟩
  let S : Fin 3 := ⟨(c i).1, by
    simpa [cup2Spec, cup2M_self_mid hn h0 htop'] using (c i).2⟩
  let R : Fin 3 := ⟨(c (right i)).1, by
    simpa [cup2Spec, cup2M_right_mid hn h0 htop' hhigh] using (c (right i)).2⟩
  have hout : cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = TMidVal L.1 S.1 R.1 := by
    simp [cup2OutVal, L, S, R, h0, h1, htop', hhigh]
  have hfc' : localFcAfter L.1 S.1 R.1 (TMidVal L.1 S.1 R.1) = localFcBefore L.1 S.1 R.1 := by
    simpa [L, S, R, hout] using hfc_local
  have hexp2' : localExp2After n i L.1 S.1 R.1 (TMidVal L.1 S.1 R.1) =
      localExp2Before n i L.1 S.1 R.1 := by
    simpa [L, S, R, hout] using hexp2
  have hi21' : localInt21After n i L.1 S.1 R.1 (TMidVal L.1 S.1 R.1) =
      localInt21Before n i L.1 S.1 R.1 := by
    simpa [L, S, R, hout] using hi21
  have hweight' : localExp2WeightAfter n i L.1 S.1 R.1 (TMidVal L.1 S.1 R.1) =
      localExp2WeightBefore n i L.1 S.1 R.1 := by
    simpa [L, S, R, hout] using hweight
  have hpriv' : TMidVal L.1 S.1 R.1 ≠ S.1 := by
    simpa [L, S, R, hout] using hpriv_val
  simpa [IsMidHopTriple, L, S, R] using
    mid_tp_zero_cases n h3 htop L S R hfc' hexp2' hi21' hweight' hpriv'

theorem cup2TpPreserving_mid_zero_left_two_false (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i : Fin n)
    (h3 : 3 ≤ i.1) (htop : i.1 + 2 < n)
    (hfc : cup2Fc n hn (move (cup2System n hn) c i) = cup2Fc n hn c)
    (htp : cup2TpPreservingMove n hn c i)
    (hpriv : privileged (cup2System n hn) c i)
    (hleft : (c (left i)).1 = 2) :
    False := by
  have hcase := cup2TpPreserving_mid_zero_cases_val n hn c i h3 htop hfc htp hpriv
  rcases hcase with h022 | h100 | h112
  · omega
  · omega
  · omega

theorem cup2TpPreserving_mid_zero_left_zero_val (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i : Fin n)
    (h3 : 3 ≤ i.1) (htop : i.1 + 2 < n)
    (hfc : cup2Fc n hn (move (cup2System n hn) c i) = cup2Fc n hn c)
    (htp : cup2TpPreservingMove n hn c i)
    (hpriv : privileged (cup2System n hn) c i)
    (hleft : (c (left i)).1 = 0) :
    (c i).1 = 2 ∧ (c (right i)).1 = 2 ∧
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = 0 := by
  have hcase := cup2TpPreserving_mid_zero_cases_val n hn c i h3 htop hfc htp hpriv
  have h0 : i.1 ≠ 0 := by omega
  have h1 : i.1 ≠ 1 := by omega
  have htop' : i.1 + 1 ≠ n := by omega
  have hhigh : i.1 + 2 ≠ n := by omega
  rcases hcase with h022 | h100 | h112
  · rcases h022 with ⟨_, hself, hright⟩
    constructor
    · exact hself
    constructor
    · exact hright
    · simp [cup2OutVal, h0, h1, htop', hhigh, hleft, hself, hright]
      native_decide
  · omega
  · omega

theorem cup2TpPreserving_mid_zero_left_one_cases_val (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i : Fin n)
    (h3 : 3 ≤ i.1) (htop : i.1 + 2 < n)
    (hfc : cup2Fc n hn (move (cup2System n hn) c i) = cup2Fc n hn c)
    (htp : cup2TpPreservingMove n hn c i)
    (hpriv : privileged (cup2System n hn) c i)
    (hleft : (c (left i)).1 = 1) :
    ((c i).1 = 0 ∧ (c (right i)).1 = 0 ∧
        cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = 1) ∨
      ((c i).1 = 1 ∧ (c (right i)).1 = 2 ∧
        cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = 2) := by
  have hcase := cup2TpPreserving_mid_zero_cases_val n hn c i h3 htop hfc htp hpriv
  have h0 : i.1 ≠ 0 := by omega
  have h1 : i.1 ≠ 1 := by omega
  have htop' : i.1 + 1 ≠ n := by omega
  have hhigh : i.1 + 2 ≠ n := by omega
  rcases hcase with h022 | h100 | h112
  · omega
  · rcases h100 with ⟨_, hself, hright⟩
    left
    constructor
    · exact hself
    constructor
    · exact hright
    · simp [cup2OutVal, h0, h1, htop', hhigh, hleft, hself, hright]
      native_decide
  · rcases h112 with ⟨_, hself, hright⟩
    right
    constructor
    · exact hself
    constructor
    · exact hright
    · simp [cup2OutVal, h0, h1, htop', hhigh, hleft, hself, hright]
      native_decide

theorem cup2TpPreserving_mid_zero_budget_drop (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i : Fin n)
    (h3 : 3 ≤ i.1) (htop : i.1 + 2 < n)
    (hfc : cup2Fc n hn (move (cup2System n hn) c i) = cup2Fc n hn c)
    (htp : cup2TpPreservingMove n hn c i)
    (hpriv : privileged (cup2System n hn) c i) :
    midHopBudget n hn (move (cup2System n hn) c i) i < midHopBudget n hn c i := by
  have h0 : i.1 ≠ 0 := by omega
  have h1 : i.1 ≠ 1 := by omega
  have htop' : i.1 + 1 ≠ n := by omega
  have hhigh : i.1 + 2 ≠ n := by omega
  have hleft_eq : (move (cup2System n hn) c i (left i)).1 = (c (left i)).1 := by
    have hn2 : 2 ≤ n := by omega
    rw [move_apply_ne n hn c i (left i) (left_ne_self hn2 i)]
  unfold midHopBudget
  rw [hleft_eq, move_apply_self_val n hn c i]
  by_cases hleft0 : (c (left i)).1 = 0
  · obtain ⟨hself, hright, hout⟩ :=
      cup2TpPreserving_mid_zero_left_zero_val n hn c i h3 htop hfc htp hpriv hleft0
    have hout' : cup2OutVal n i 0 2 2 = 0 := by
      simpa [hleft0, hself, hright] using hout
    rw [hleft0, hself, hright, hout']
    simp [midHopBudgetVal]
  · by_cases hleft1 : (c (left i)).1 = 1
    · rcases cup2TpPreserving_mid_zero_left_one_cases_val n hn c i h3 htop hfc htp hpriv hleft1 with
        h100 | h112
      · rcases h100 with ⟨hself, hright, hout⟩
        have hout' : cup2OutVal n i 1 0 0 = 1 := by
          simpa [hleft1, hself, hright] using hout
        rw [hleft1, hself, hright, hout']
        simp [midHopBudgetVal]
      · rcases h112 with ⟨hself, hright, hout⟩
        have hout' : cup2OutVal n i 1 1 2 = 2 := by
          simpa [hleft1, hself, hright] using hout
        rw [hleft1, hself, hright, hout']
        simp [midHopBudgetVal]
    · have hleft2 : (c (left i)).1 = 2 := by
        have hlt : (c (left i)).1 < 3 := by
          simpa [cup2Spec, cup2M_left_mid hn h0 h1 htop'] using (c (left i)).2
        omega
      exact False.elim <|
        cup2TpPreserving_mid_zero_left_two_false n hn c i h3 htop hfc htp hpriv hleft2

theorem cup2MidTpZeroStepAt_budget_drop (n : Nat) (hn : 4 ≤ n) (i : Fin n)
    (h3 : 3 ≤ i.1) (htop : i.1 + 2 < n)
    {c' c : Config (cup2Spec n hn)}
    (hstep : cup2MidTpZeroStepAt n hn i c' c) :
    midHopBudget n hn c' i < midHopBudget n hn c i := by
  rcases hstep with ⟨hpriv, rfl, hfc, htp⟩
  exact cup2TpPreserving_mid_zero_budget_drop n hn c i h3 htop hfc htp hpriv

theorem cup2MidTpZeroStepAt_wf (n : Nat) (hn : 4 ≤ n) (i : Fin n)
    (h3 : 3 ≤ i.1) (htop : i.1 + 2 < n) :
    WellFounded (cup2MidTpZeroStepAt n hn i) := by
  let r : Config (cup2Spec n hn) → Config (cup2Spec n hn) → Prop :=
    InvImage (· < ·) (fun c => midHopBudget n hn c i)
  refine Subrelation.wf (r := r) ?_ ?_
  · intro c' c hstep
    exact cup2MidTpZeroStepAt_budget_drop n hn i h3 htop hstep
  · exact InvImage.wf (fun c => midHopBudget n hn c i) Nat.lt_wfRel.wf

def deepMidHopWeight (n : Nat) (i : Fin n) : Nat :=
  3 ^ (n - 1 - i.1)

def deepMidHopPotentialTerm (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i : Fin n) : Nat :=
  deepMidHopWeight n i * midHopBudget n hn c i

def deepMidHopPotential (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) : Nat :=
  ∑ i : Fin n, deepMidHopPotentialTerm n hn c i

def hopAdjacentComplement {n : Nat} (i : Fin n) : Finset (Fin n) :=
  (Finset.univ.erase i).erase (right i)

lemma mem_hopAdjacentComplement_iff {n : Nat} (i j : Fin n) :
    j ∈ hopAdjacentComplement i ↔ j ≠ i ∧ j ≠ right i := by
  unfold hopAdjacentComplement
  simp [and_comm]

lemma left_ne_of_mem_hopAdjacentComplement {n : Nat} (hn : 2 ≤ n) (i j : Fin n)
    (hj : j ∈ hopAdjacentComplement i) :
    left j ≠ i := by
  have hjr : j ≠ right i := (mem_hopAdjacentComplement_iff i j).mp hj |>.2
  intro hleft
  apply hjr
  calc
    j = right (left j) := by symm; exact right_left hn j
    _ = right i := by simpa [hleft]

lemma sum_univ_eq_hopAdjacentComplement {n : Nat} {α : Type*} [AddCommMonoid α]
    (hn : 2 ≤ n) (f : Fin n → α) (i : Fin n) :
    (∑ j : Fin n, f j) = f i + f (right i) + Finset.sum (hopAdjacentComplement i) f := by
  unfold hopAdjacentComplement
  rw [← Finset.add_sum_erase (Finset.univ) f (Finset.mem_univ i)]
  have hrightmem : right i ∈ Finset.univ.erase i := by
    simp [right_ne_self hn i]
  rw [← Finset.add_sum_erase (Finset.univ.erase i) f hrightmem]
  simp [add_left_comm, add_comm]

lemma deepMidHopWeight_pos (n : Nat) (i : Fin n) :
    0 < deepMidHopWeight n i := by
  simpa [deepMidHopWeight] using pow_pos (show 0 < (3 : Nat) by decide) (n - 1 - i.1)

lemma deepMidHopWeight_eq_three_mul_right (n : Nat) {i : Fin n}
    (htop : i.1 + 1 ≠ n) :
    deepMidHopWeight n i = 3 * deepMidHopWeight n (right i) := by
  have hright : (right i).1 = i.1 + 1 := right_val_of_not_top htop
  unfold deepMidHopWeight
  rw [hright]
  have hexp : n - 1 - i.1 = (n - 1 - (i.1 + 1)) + 1 := by
    omega
  rw [hexp, Nat.pow_succ]
  ring

lemma deepMidHopPotentialTerm_move_eq_of_mem_hopAdjacentComplement (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i j : Fin n) (hj : j ∈ hopAdjacentComplement i) :
    deepMidHopPotentialTerm n hn (move (cup2System n hn) c i) j =
      deepMidHopPotentialTerm n hn c j := by
  have hn2 : 2 ≤ n := by omega
  have hji : j ≠ i := (mem_hopAdjacentComplement_iff i j).mp hj |>.1
  have hleft : left j ≠ i := left_ne_of_mem_hopAdjacentComplement hn2 i j hj
  unfold deepMidHopPotentialTerm midHopBudget
  simp [move, hji, hleft]

lemma deepMidHopPotential_split (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i : Fin n) :
    deepMidHopPotential n hn c =
      deepMidHopPotentialTerm n hn c i +
        deepMidHopPotentialTerm n hn c (right i) +
          Finset.sum (hopAdjacentComplement i) (deepMidHopPotentialTerm n hn c) := by
  have hn2 : 2 ≤ n := by omega
  rw [deepMidHopPotential,
    sum_univ_eq_hopAdjacentComplement hn2 (deepMidHopPotentialTerm n hn c) i]

lemma deepMidHopPotential_move_split (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i : Fin n) :
    deepMidHopPotential n hn (move (cup2System n hn) c i) =
      deepMidHopPotentialTerm n hn (move (cup2System n hn) c i) i +
        deepMidHopPotentialTerm n hn (move (cup2System n hn) c i) (right i) +
          Finset.sum (hopAdjacentComplement i)
            (deepMidHopPotentialTerm n hn (move (cup2System n hn) c i)) := by
  have hn2 : 2 ≤ n := by omega
  rw [deepMidHopPotential,
    sum_univ_eq_hopAdjacentComplement hn2
      (deepMidHopPotentialTerm n hn (move (cup2System n hn) c i)) i]

lemma deepMidHopPotential_rest_move_eq (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i : Fin n) :
    Finset.sum (hopAdjacentComplement i)
        (deepMidHopPotentialTerm n hn (move (cup2System n hn) c i)) =
      Finset.sum (hopAdjacentComplement i) (deepMidHopPotentialTerm n hn c) := by
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact deepMidHopPotentialTerm_move_eq_of_mem_hopAdjacentComplement n hn c i j hj

theorem cup2TpPreserving_mid_zero_local_potential_drop (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i : Fin n)
    (h3 : 3 ≤ i.1) (htop : i.1 + 2 < n)
    (hfc : cup2Fc n hn (move (cup2System n hn) c i) = cup2Fc n hn c)
    (htp : cup2TpPreservingMove n hn c i)
    (hpriv : privileged (cup2System n hn) c i) :
    deepMidHopPotentialTerm n hn (move (cup2System n hn) c i) i +
        deepMidHopPotentialTerm n hn (move (cup2System n hn) c i) (right i) <
      deepMidHopPotentialTerm n hn c i +
        deepMidHopPotentialTerm n hn c (right i) := by
  have hn2 : 2 ≤ n := by omega
  have h0 : i.1 ≠ 0 := by omega
  have h1 : i.1 ≠ 1 := by omega
  have htop' : i.1 + 1 ≠ n := by omega
  have hhigh : i.1 + 2 ≠ n := by omega
  have hri : right i ≠ i := right_ne_self hn2 i
  have hlefti : left i ≠ i := left_ne_self hn2 i
  have hleftright : left (right i) = i := left_right hn2 i
  have hrightval : (right i).1 = i.1 + 1 := right_val_of_not_top htop'
  have hpow : 3 ^ (n - 1 - i.1) = 3 * 3 ^ (n - 1 - (i.1 + 1)) := by
    have hexp : n - 1 - i.1 = (n - 1 - (i.1 + 1)) + 1 := by
      omega
    rw [hexp, Nat.pow_succ]
    ring
  have hpow_pos : 0 < 3 ^ (n - 1 - (i.1 + 1)) := by
    exact pow_pos (show 0 < (3 : Nat) by decide) _
  by_cases hleft0 : (c (left i)).1 = 0
  · obtain ⟨hself, hright, hout⟩ :=
      cup2TpPreserving_mid_zero_left_zero_val n hn c i h3 htop hfc htp hpriv hleft0
    have hout' : cup2OutVal n i 0 2 2 = 0 := by
      simpa [hleft0, hself, hright] using hout
    unfold deepMidHopPotentialTerm deepMidHopWeight midHopBudget
    rw [hpow]
    rw [move_apply_ne n hn c i (left i) hlefti, move_apply_self_val n hn c i,
      hleftright, move_apply_ne n hn c i (right i) hri, hrightval]
    simp [hleft0, hself, hright, hout', midHopBudgetVal]
  · by_cases hleft1 : (c (left i)).1 = 1
    · rcases cup2TpPreserving_mid_zero_left_one_cases_val n hn c i h3 htop hfc htp hpriv hleft1 with
        h100 | h112
      · rcases h100 with ⟨hself, hright, hout⟩
        have hout' : cup2OutVal n i 1 0 0 = 1 := by
          simpa [hleft1, hself, hright] using hout
        unfold deepMidHopPotentialTerm deepMidHopWeight midHopBudget
        rw [hpow]
        rw [move_apply_ne n hn c i (left i) hlefti, move_apply_self_val n hn c i,
          hleftright, move_apply_ne n hn c i (right i) hri, hrightval]
        simp [hleft1, hself, hright, hout', midHopBudgetVal]
        nlinarith [hpow_pos]
      · rcases h112 with ⟨hself, hright, hout⟩
        have hout' : cup2OutVal n i 1 1 2 = 2 := by
          simpa [hleft1, hself, hright] using hout
        unfold deepMidHopPotentialTerm deepMidHopWeight midHopBudget
        rw [hpow]
        rw [move_apply_ne n hn c i (left i) hlefti, move_apply_self_val n hn c i,
          hleftright, move_apply_ne n hn c i (right i) hri, hrightval]
        simp [hleft1, hself, hright, hout', midHopBudgetVal]
    · have hleft2 : (c (left i)).1 = 2 := by
        have hlt : (c (left i)).1 < 3 := by
          simpa [cup2Spec, cup2M_left_mid hn h0 h1 htop'] using (c (left i)).2
        omega
      exact False.elim <|
        cup2TpPreserving_mid_zero_left_two_false n hn c i h3 htop hfc htp hpriv hleft2

theorem cup2TpPreserving_mid_zero_potential_drop (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i : Fin n)
    (h3 : 3 ≤ i.1) (htop : i.1 + 2 < n)
    (hfc : cup2Fc n hn (move (cup2System n hn) c i) = cup2Fc n hn c)
    (htp : cup2TpPreservingMove n hn c i)
    (hpriv : privileged (cup2System n hn) c i) :
    deepMidHopPotential n hn (move (cup2System n hn) c i) <
      deepMidHopPotential n hn c := by
  rw [deepMidHopPotential_move_split n hn c i, deepMidHopPotential_split n hn c i,
    deepMidHopPotential_rest_move_eq n hn c i]
  simpa [add_assoc] using
    Nat.add_lt_add_right
      (cup2TpPreserving_mid_zero_local_potential_drop n hn c i h3 htop hfc htp hpriv)
      (Finset.sum (hopAdjacentComplement i) (deepMidHopPotentialTerm n hn c))

def cup2DeepMidTpZeroStep (n : Nat) (hn : 4 ≤ n)
    (c' c : Config (cup2Spec n hn)) : Prop :=
  ∃ i, 3 ≤ i.1 ∧ i.1 + 2 < n ∧ cup2MidTpZeroStepAt n hn i c' c

theorem cup2DeepMidTpZeroStep_potential_drop (n : Nat) (hn : 4 ≤ n)
    {c' c : Config (cup2Spec n hn)}
    (hstep : cup2DeepMidTpZeroStep n hn c' c) :
    deepMidHopPotential n hn c' < deepMidHopPotential n hn c := by
  rcases hstep with ⟨i, h3, htop, hstep⟩
  rcases hstep with ⟨hpriv, rfl, hfc, htp⟩
  exact cup2TpPreserving_mid_zero_potential_drop n hn c i h3 htop hfc htp hpriv

theorem cup2DeepMidTpZeroStep_wf (n : Nat) (hn : 4 ≤ n) :
    WellFounded (cup2DeepMidTpZeroStep n hn) := by
  let r : Config (cup2Spec n hn) → Config (cup2Spec n hn) → Prop :=
    InvImage (· < ·) (deepMidHopPotential n hn)
  refine Subrelation.wf (r := r) ?_ ?_
  · intro c' c hstep
    exact cup2DeepMidTpZeroStep_potential_drop n hn hstep
  · exact InvImage.wf (deepMidHopPotential n hn) Nat.lt_wfRel.wf

theorem cup2TpPreserving_zero_fc_step_boundary_or_deep (n : Nat) (hn : 4 ≤ n)
    {c c' : Config (cup2Spec n hn)}
    (hstep : step (cup2System n hn) c c')
    (hfc : cup2Fc n hn c' = cup2Fc n hn c)
    (htp : cup2TpInvariant n hn c' = cup2TpInvariant n hn c) :
    (∃ i, privileged (cup2System n hn) c i ∧
        c' = move (cup2System n hn) c i ∧
          (i.1 ≤ 2 ∨ n - 3 ≤ i.1)) ∨
      cup2DeepMidTpZeroStep n hn c' c := by
  rcases hstep with ⟨i, hpriv, rfl⟩
  by_cases hboundary : i.1 ≤ 2 ∨ n - 3 ≤ i.1
  · left
    exact ⟨i, hpriv, rfl, hboundary⟩
  · right
    refine ⟨i, ?_, ?_, ?_⟩
    · omega
    · omega
    · exact ⟨hpriv, rfl, hfc, htp⟩

end LeanMn
