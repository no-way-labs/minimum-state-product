import LeanMn.Convergence.CopyDAG

namespace LeanMn

lemma bot_drop_from_one_cases (L : Fin 2) (R : Fin 3)
    (h : TBotVal L.1 1 R.1 = 0) :
    (L.1 = 1 ∧ R.1 = 0) ∨ (L.1 = 1 ∧ R.1 = 2) := by
  fin_cases L <;> fin_cases R <;> simp [TBotVal] at h ⊢

lemma bot_left_zero_self_one_stable (R : Fin 3) :
    TBotVal 0 1 R.1 = 1 := by
  fin_cases R <;> decide

lemma low_zero_two_exact (R : Fin 3) :
    TLowVal 0 2 R.1 = if R.1 = 1 then 2 else 0 := by
  fin_cases R <;> decide

lemma top_zero_self_one_drop (R : Fin 2) :
    TTopVal 0 1 R.1 = 0 := by
  fin_cases R <;> decide

lemma top_rise_copy_cases (L : Fin 3)
    (h : TTopVal L.1 0 1 = 1) :
    L.1 = 1 ∨ L.1 = 2 := by
  fin_cases L <;> simp [TTopVal] at h ⊢

lemma top_drop_from_one_requires_left_zero (L : Fin 3) (R : Fin 2)
    (h : TTopVal L.1 1 R.1 = 0) :
    L.1 = 0 := by
  fin_cases L <;> fin_cases R <;> simp [TTopVal] at h ⊢

lemma high_output_two_transition_cases (L S : Fin 3) (R : Fin 2)
    (hout : THighVal L.1 S.1 R.1 = 2) (hmove : S.1 ≠ 2) :
    (L.1 = 1 ∧ S.1 = 1 ∧ R.1 = 1) ∨
      (L.1 = 2 ∧ S.1 = 0 ∧ R.1 = 1) ∨
      (L.1 = 2 ∧ S.1 = 1 ∧ R.1 = 1) := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [THighVal] at hout hmove ⊢

lemma high_output_two_transition_requires_right_one (L S : Fin 3) (R : Fin 2)
    (hout : THighVal L.1 S.1 R.1 = 2) (hmove : S.1 ≠ 2) :
    R.1 = 1 := by
  rcases high_output_two_transition_cases L S R hout hmove with h | h | h <;> omega

lemma high_drop_from_two_cases (L : Fin 3) (R : Fin 2)
    (h : THighVal L.1 2 R.1 = 0) :
    (L.1 = 0 ∧ R.1 = 0) ∨ (L.1 = 0 ∧ R.1 = 1) ∨ (L.1 = 1 ∧ R.1 = 0) := by
  fin_cases L <;> fin_cases R <;> simp [THighVal] at h ⊢

lemma high_rise_from_zero_cases (L : Fin 3) (R : Fin 2)
    (h : THighVal L.1 0 R.1 = 1) :
    (L.1 = 1 ∧ R.1 = 0) ∨ (L.1 = 1 ∧ R.1 = 1) := by
  fin_cases L <;> fin_cases R <;> simp [THighVal] at h ⊢

lemma bot_output_zero_self_one_cases_val (n : Nat) (hn : 4 ≤ n) {i : Fin n}
    (h0 : i.1 = 0) (c : Config (cup2Spec n hn)) (hself : (c i).1 = 1)
    (hout : cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = 0) :
    ((c (left i)).1 = 1 ∧ (c (right i)).1 = 0) ∨
      ((c (left i)).1 = 1 ∧ (c (right i)).1 = 2) := by
  let L : Fin 2 := ⟨(c (left i)).1, by
    simpa [cup2Spec, cup2M_left_bot hn h0] using (c (left i)).2⟩
  let R : Fin 3 := ⟨(c (right i)).1, by
    simpa [cup2Spec, cup2M_right_bot hn h0] using (c (right i)).2⟩
  have hout' : TBotVal L.1 1 R.1 = 0 := by
    simpa [L, R, cup2OutVal, h0, hself] using hout
  simpa [L, R] using bot_drop_from_one_cases L R hout'

lemma top_output_zero_self_one_requires_left_zero_val (n : Nat) (hn : 4 ≤ n) {i : Fin n}
    (htop : i.1 + 1 = n) (c : Config (cup2Spec n hn)) (hself : (c i).1 = 1)
    (hout : cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = 0) :
    (c (left i)).1 = 0 := by
  let L : Fin 3 := ⟨(c (left i)).1, by
    simpa [cup2Spec, cup2M_left_top hn htop] using (c (left i)).2⟩
  let R : Fin 2 := ⟨(c (right i)).1, by
    simpa [cup2Spec, cup2M_right_top hn htop] using (c (right i)).2⟩
  have h0 : i.1 ≠ 0 := by omega
  have h1 : i.1 ≠ 1 := by omega
  have hout' : TTopVal L.1 1 R.1 = 0 := by
    simpa [L, R, cup2OutVal, h0, h1, htop, hself] using hout
  simpa [L] using top_drop_from_one_requires_left_zero L R hout'

lemma top_output_one_self_zero_right_one_cases_val (n : Nat) (hn : 4 ≤ n) {i : Fin n}
    (htop : i.1 + 1 = n) (c : Config (cup2Spec n hn)) (hself : (c i).1 = 0)
    (hright : (c (right i)).1 = 1)
    (hout : cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = 1) :
    (c (left i)).1 = 1 ∨ (c (left i)).1 = 2 := by
  let L : Fin 3 := ⟨(c (left i)).1, by
    simpa [cup2Spec, cup2M_left_top hn htop] using (c (left i)).2⟩
  have h0 : i.1 ≠ 0 := by omega
  have h1 : i.1 ≠ 1 := by omega
  have hout' : TTopVal L.1 0 1 = 1 := by
    simpa [L, cup2OutVal, h0, h1, htop, hself, hright] using hout
  simpa [L] using top_rise_copy_cases L hout'

lemma high_output_two_transition_requires_right_one_val (n : Nat) (hn : 4 ≤ n) {i : Fin n}
    (hhigh : i.1 + 2 = n) (c : Config (cup2Spec n hn)) (hself_ne : (c i).1 ≠ 2)
    (hout : cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = 2) :
    (c (right i)).1 = 1 := by
  let L : Fin 3 := ⟨(c (left i)).1, by
    simpa [cup2Spec, cup2M_left_high hn hhigh] using (c (left i)).2⟩
  let S : Fin 3 := ⟨(c i).1, by
    simpa [cup2Spec, cup2M_self_high hn hhigh] using (c i).2⟩
  let R : Fin 2 := ⟨(c (right i)).1, by
    simpa [cup2Spec, cup2M_right_high hn hhigh] using (c (right i)).2⟩
  have h0 : i.1 ≠ 0 := by omega
  have h1 : i.1 ≠ 1 := by omega
  have htop : i.1 + 1 ≠ n := by omega
  have hout' : THighVal L.1 S.1 R.1 = 2 := by
    simpa [L, S, R, cup2OutVal, h0, h1, htop, hhigh] using hout
  have hmove' : S.1 ≠ 2 := by simpa [S] using hself_ne
  have hR1 : R.1 = 1 := high_output_two_transition_requires_right_one L S R hout' hmove'
  simpa [R] using hR1

lemma bot_positive_cases (L : Fin 2) (S : Fin 2) (R : Fin 3)
    (hfc : localFcBefore L.1 S.1 R.1 < localFcAfter L.1 S.1 R.1 (TBotVal L.1 S.1 R.1))
    (hpriv : TBotVal L.1 S.1 R.1 ≠ S.1) :
    (L.1 = 0 ∧ S.1 = 0 ∧ R.1 = 0) ∨ (L.1 = 1 ∧ S.1 = 1 ∧ R.1 = 2) := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [localFcAfter, localFcBefore, frontierBitVal, TBotVal] at hfc hpriv ⊢

lemma low_positive_cases (L : Fin 2) (S : Fin 3) (R : Fin 3)
    (hfc : localFcBefore L.1 S.1 R.1 < localFcAfter L.1 S.1 R.1 (TLowVal L.1 S.1 R.1))
    (hpriv : TLowVal L.1 S.1 R.1 ≠ S.1) :
    False := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [localFcAfter, localFcBefore, frontierBitVal, TLowVal] at hfc hpriv

lemma mid_positive_cases (L S R : Fin 3)
    (hfc : localFcBefore L.1 S.1 R.1 < localFcAfter L.1 S.1 R.1 (TMidVal L.1 S.1 R.1))
    (hpriv : TMidVal L.1 S.1 R.1 ≠ S.1) :
    L.1 = 2 ∧ S.1 = 1 ∧ R.1 = 1 := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [localFcAfter, localFcBefore, frontierBitVal, TMidVal] at hfc hpriv ⊢ <;>
    omega

lemma high_positive_cases (L S : Fin 3) (R : Fin 2)
    (hfc : localFcBefore L.1 S.1 R.1 < localFcAfter L.1 S.1 R.1 (THighVal L.1 S.1 R.1))
    (hpriv : THighVal L.1 S.1 R.1 ≠ S.1) :
    L.1 = 1 ∧ S.1 = 1 ∧ R.1 = 1 := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [localFcAfter, localFcBefore, frontierBitVal, THighVal] at hfc hpriv ⊢

lemma top_positive_cases (L : Fin 3) (S R : Fin 2)
    (hfc : localFcBefore L.1 S.1 R.1 < localFcAfter L.1 S.1 R.1 (TTopVal L.1 S.1 R.1))
    (hpriv : TTopVal L.1 S.1 R.1 ≠ S.1) :
    L.1 = 2 ∧ S.1 = 0 ∧ R.1 = 0 := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [localFcAfter, localFcBefore, frontierBitVal, TTopVal] at hfc hpriv ⊢

lemma localFc_lt_of_fc_lt_move (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n)
    (hfc : cup2Fc n hn c < cup2Fc n hn (move (cup2System n hn) c i)) :
    localFcBefore (c (left i)).1 (c i).1 (c (right i)).1 <
      localFcAfter (c (left i)).1 (c i).1 (c (right i)).1
        (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) := by
  rw [cup2Fc_move_split n hn c i, cup2Fc_split n hn c i, cup2Fc_rest_move_eq n hn c i] at hfc
  omega

def IsB1Config (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) : Prop :=
  i.1 = 0 ∧ (c (left i)).1 = 0 ∧ (c i).1 = 0 ∧ (c (right i)).1 = 0

def IsB2Config (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) : Prop :=
  i.1 = 0 ∧ (c (left i)).1 = 1 ∧ (c i).1 = 1 ∧ (c (right i)).1 = 2

def IsB3Config (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) : Prop :=
  i.1 + 2 = n ∧ (c (left i)).1 = 1 ∧ (c i).1 = 1 ∧ (c (right i)).1 = 1

def IsB4Config (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) : Prop :=
  i.1 + 1 = n ∧ (c (left i)).1 = 2 ∧ (c i).1 = 0 ∧ (c (right i)).1 = 0

/-- B5: TMid anomalous entry from liveness fix. TMidVal(2,1,1) = 0. -/
def IsB5Config (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) : Prop :=
  2 ≤ i.1 ∧ i.1 + 2 < n ∧ (c (left i)).1 = 2 ∧ (c i).1 = 1 ∧ (c (right i)).1 = 1

def cup2BadStepPos (n : Nat) (hn : 4 ≤ n)
    (c' c : Config (cup2Spec n hn)) : Prop :=
  badStep (cup2System n hn) (cup2GoodCycle n hn) c' c ∧ cup2Fc n hn c < cup2Fc n hn c'

def cup2BadStepNeg (n : Nat) (hn : 4 ≤ n)
    (c' c : Config (cup2Spec n hn)) : Prop :=
  badStep (cup2System n hn) (cup2GoodCycle n hn) c' c ∧ cup2Fc n hn c' < cup2Fc n hn c

theorem cup2Move_fc_increase_cases (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i : Fin n)
    (hpriv : privileged (cup2System n hn) c i)
    (hfc : cup2Fc n hn c < cup2Fc n hn (move (cup2System n hn) c i)) :
    IsB1Config n hn c i ∨ IsB2Config n hn c i ∨
      IsB3Config n hn c i ∨ IsB4Config n hn c i ∨ IsB5Config n hn c i := by
  have hpriv_val :
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 ≠ (c i).1 := by
    simpa [privileged, cup2System, cup2Trans_val, Fin.ne_iff_vne] using hpriv
  have hfc_local := localFc_lt_of_fc_lt_move n hn c i hfc
  by_cases h0 : i.1 = 0
  · let L : Fin 2 := ⟨(c (left i)).1, by
      simpa [cup2Spec, cup2M_left_bot hn h0] using (c (left i)).2⟩
    let S : Fin 2 := ⟨(c i).1, by
      simpa [cup2Spec, cup2M_eq_two_of_endpoint (n := n) (i := i) (Or.inl h0)] using (c i).2⟩
    let R : Fin 3 := ⟨(c (right i)).1, by
      simpa [cup2Spec, cup2M_right_bot hn h0] using (c (right i)).2⟩
    have hfc' : localFcBefore L.1 S.1 R.1 < localFcAfter L.1 S.1 R.1 (TBotVal L.1 S.1 R.1) := by
      simpa [L, S, R, cup2OutVal, h0] using hfc_local
    have hpriv' : TBotVal L.1 S.1 R.1 ≠ S.1 := by
      simpa [L, S, R, cup2OutVal, h0] using hpriv_val
    rcases bot_positive_cases L S R hfc' hpriv' with hcase | hcase
    · rcases hcase with ⟨hL, hS, hR⟩
      left
      exact ⟨h0, by simpa [L] using hL, by simpa [S] using hS, by simpa [R] using hR⟩
    · rcases hcase with ⟨hL, hS, hR⟩
      right; left
      exact ⟨h0, by simpa [L] using hL, by simpa [S] using hS, by simpa [R] using hR⟩
  · by_cases h1 : i.1 = 1
    · let L : Fin 2 := ⟨(c (left i)).1, by
        simpa [cup2Spec, cup2M_left_low hn h1] using (c (left i)).2⟩
      let S : Fin 3 := ⟨(c i).1, by
        simpa [cup2Spec, cup2M_self_low hn h1] using (c i).2⟩
      let R : Fin 3 := ⟨(c (right i)).1, by
        simpa [cup2Spec, cup2M_right_low hn h1] using (c (right i)).2⟩
      have hfc' : localFcBefore L.1 S.1 R.1 < localFcAfter L.1 S.1 R.1 (TLowVal L.1 S.1 R.1) := by
        simpa [L, S, R, cup2OutVal, h0, h1] using hfc_local
      have hpriv' : TLowVal L.1 S.1 R.1 ≠ S.1 := by
        simpa [L, S, R, cup2OutVal, h0, h1] using hpriv_val
      exact False.elim (low_positive_cases L S R hfc' hpriv')
    · by_cases htop : i.1 + 1 = n
      · let L : Fin 3 := ⟨(c (left i)).1, by
          simpa [cup2Spec, cup2M_left_top hn htop] using (c (left i)).2⟩
        let S : Fin 2 := ⟨(c i).1, by
          simpa [cup2Spec, cup2M_eq_two_of_endpoint (n := n) (i := i) (Or.inr htop)] using (c i).2⟩
        let R : Fin 2 := ⟨(c (right i)).1, by
          simpa [cup2Spec, cup2M_right_top hn htop] using (c (right i)).2⟩
        have hfc' : localFcBefore L.1 S.1 R.1 < localFcAfter L.1 S.1 R.1 (TTopVal L.1 S.1 R.1) := by
          simpa [L, S, R, cup2OutVal, h0, h1, htop] using hfc_local
        have hpriv' : TTopVal L.1 S.1 R.1 ≠ S.1 := by
          simpa [L, S, R, cup2OutVal, h0, h1, htop] using hpriv_val
        rcases top_positive_cases L S R hfc' hpriv' with ⟨hL, hS, hR⟩
        right
        right
        right
        left
        exact ⟨htop, by simpa [L] using hL, by simpa [S] using hS, by simpa [R] using hR⟩
      · by_cases hhigh : i.1 + 2 = n
        · let L : Fin 3 := ⟨(c (left i)).1, by
            simpa [cup2Spec, cup2M_left_high hn hhigh] using (c (left i)).2⟩
          let S : Fin 3 := ⟨(c i).1, by
            simpa [cup2Spec, cup2M_self_high hn hhigh] using (c i).2⟩
          let R : Fin 2 := ⟨(c (right i)).1, by
            simpa [cup2Spec, cup2M_right_high hn hhigh] using (c (right i)).2⟩
          have hfc' : localFcBefore L.1 S.1 R.1 < localFcAfter L.1 S.1 R.1 (THighVal L.1 S.1 R.1) := by
            simpa [L, S, R, cup2OutVal, h0, h1, htop, hhigh] using hfc_local
          have hpriv' : THighVal L.1 S.1 R.1 ≠ S.1 := by
            simpa [L, S, R, cup2OutVal, h0, h1, htop, hhigh] using hpriv_val
          rcases high_positive_cases L S R hfc' hpriv' with ⟨hL, hS, hR⟩
          right; right; left
          exact ⟨hhigh, by simpa [L] using hL, by simpa [S] using hS, by simpa [R] using hR⟩
        · let L : Fin 3 := ⟨(c (left i)).1, by
            simpa [cup2Spec, cup2M_left_mid hn h0 h1 htop] using (c (left i)).2⟩
          let S : Fin 3 := ⟨(c i).1, by
            simpa [cup2Spec, cup2M_self_mid hn h0 htop] using (c i).2⟩
          let R : Fin 3 := ⟨(c (right i)).1, by
            simpa [cup2Spec, cup2M_right_mid hn h0 htop hhigh] using (c (right i)).2⟩
          have hfc' : localFcBefore L.1 S.1 R.1 < localFcAfter L.1 S.1 R.1 (TMidVal L.1 S.1 R.1) := by
            simpa [L, S, R, cup2OutVal, h0, h1, htop, hhigh] using hfc_local
          have hpriv' : TMidVal L.1 S.1 R.1 ≠ S.1 := by
            simpa [L, S, R, cup2OutVal, h0, h1, htop, hhigh] using hpriv_val
          rcases mid_positive_cases L S R hfc' hpriv' with ⟨hL, hS, hR⟩
          right; right; right; right
          exact ⟨by omega, by omega,
            by simpa [L] using hL, by simpa [S] using hS, by simpa [R] using hR⟩

theorem cup2Step_fc_increase_cases (n : Nat) (hn : 4 ≤ n)
    {c c' : Config (cup2Spec n hn)}
    (hstep : step (cup2System n hn) c c')
    (hfc : cup2Fc n hn c < cup2Fc n hn c') :
    ∃ i, c' = move (cup2System n hn) c i ∧
      (IsB1Config n hn c i ∨ IsB2Config n hn c i ∨
        IsB3Config n hn c i ∨ IsB4Config n hn c i ∨ IsB5Config n hn c i) := by
  rcases hstep with ⟨i, hpriv, rfl⟩
  exact ⟨i, rfl, cup2Move_fc_increase_cases n hn c i hpriv hfc⟩

theorem cup2BadStep_cases (n : Nat) (hn : 4 ≤ n)
    {c' c : Config (cup2Spec n hn)}
    (hbad : badStep (cup2System n hn) (cup2GoodCycle n hn) c' c) :
    cup2BadStepNonneg n hn c' c ∨ cup2BadStepNeg n hn c' c := by
  by_cases hle : cup2Fc n hn c ≤ cup2Fc n hn c'
  · left
    exact ⟨hbad, hle⟩
  · right
    exact ⟨hbad, lt_of_not_ge hle⟩

theorem cup2BadStepPos_classified (n : Nat) (hn : 4 ≤ n)
    {c' c : Config (cup2Spec n hn)}
    (hbad : cup2BadStepPos n hn c' c) :
    ∃ i, c' = move (cup2System n hn) c i ∧
      (IsB1Config n hn c i ∨ IsB2Config n hn c i ∨
        IsB3Config n hn c i ∨ IsB4Config n hn c i ∨ IsB5Config n hn c i) := by
  rcases hbad with ⟨hbad, hfc⟩
  rcases hbad with ⟨_hc'_bad, _hc_bad, hstep⟩
  exact cup2Step_fc_increase_cases n hn hstep hfc

theorem cup2BadStepNeg_wf (n : Nat) (hn : 4 ≤ n) :
    WellFounded (cup2BadStepNeg n hn) := by
  let r : Config (cup2Spec n hn) → Config (cup2Spec n hn) → Prop :=
    InvImage (· < ·) (cup2Fc n hn)
  refine Subrelation.wf (r := r) ?_ ?_
  · intro c' c hstep
    exact hstep.2
  · exact InvImage.wf (cup2Fc n hn) Nat.lt_wfRel.wf

end LeanMn
