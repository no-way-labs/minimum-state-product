import LeanMn.System

namespace LeanMn

def cup2CycleLen (n : Nat) : Nat :=
  3 * n - 2

def cup2CycleVal (n t j : Nat) : Nat :=
  if _ht1 : t < n then
    if j < t then 1 else 0
  else if _ht2 : t < 2 * n - 2 then
    if j < 2 * n - 1 - t then 1 else if j < n - 1 then 2 else 1
  else if _hboundary : t = 2 * n - 2 then
    if j = 0 then 1 else if j < n - 1 then 2 else 1
  else
    let k := t - (2 * n - 2)
    if k = 0 then
      if j = 0 then 1 else if j < n - 1 then 2 else 1
    else if j < k then 0 else if j < n - 1 then 2 else 1

def cup2CycleMoverVal (n t : Nat) : Nat :=
  if _ht1 : t < n then
    t
  else if _ht2 : t < 2 * n - 2 then
    2 * n - 2 - t
  else
    t - (2 * n - 2)

lemma cup2CycleVal_phase1 (ht : t < n) :
    cup2CycleVal n t j = if j < t then 1 else 0 := by
  simp [cup2CycleVal, ht]

lemma cup2CycleVal_phase2 (ht1 : ¬ t < n) (ht2 : t < 2 * n - 2) :
    cup2CycleVal n t j = if j < 2 * n - 1 - t then 1 else if j < n - 1 then 2 else 1 := by
  simp [cup2CycleVal, ht1, ht2]

lemma cup2CycleVal_phase3_boundary (ht1 : ¬ t < n) (ht2 : ¬ t < 2 * n - 2)
    (hboundary : t = 2 * n - 2) :
    cup2CycleVal n t j = if j = 0 then 1 else if j < n - 1 then 2 else 1 := by
  subst t
  have hnot1 : ¬ 2 * n - 2 < n := by
    omega
  simp [cup2CycleVal, hnot1]

lemma cup2CycleVal_phase3 (ht1 : ¬ t < n) (ht2 : ¬ t < 2 * n - 2)
    (hboundary : t ≠ 2 * n - 2) :
    cup2CycleVal n t j =
      let k := t - (2 * n - 2)
      if k = 0 then
        if j = 0 then 1 else if j < n - 1 then 2 else 1
      else if j < k then 0 else if j < n - 1 then 2 else 1 := by
  simp [cup2CycleVal, ht1, ht2, hboundary]

lemma cup2CycleMoverVal_phase1 (ht : t < n) :
    cup2CycleMoverVal n t = t := by
  simp [cup2CycleMoverVal, ht]

lemma cup2CycleMoverVal_phase2 (ht1 : ¬ t < n) (ht2 : t < 2 * n - 2) :
    cup2CycleMoverVal n t = 2 * n - 2 - t := by
  simp [cup2CycleMoverVal, ht1, ht2]

lemma cup2CycleMoverVal_phase3 (ht1 : ¬ t < n) (ht2 : ¬ t < 2 * n - 2) :
    cup2CycleMoverVal n t = t - (2 * n - 2) := by
  simp [cup2CycleMoverVal, ht1, ht2]

lemma cup2CycleVal_le_two (n : Nat) (t : Fin (cup2CycleLen n)) (j : Fin n) :
    cup2CycleVal n t.1 j.1 ≤ 2 := by
  unfold cup2CycleVal cup2CycleLen
  repeat' (first | split_ifs with h | simp_all)

lemma cup2CycleVal_endpoint_lt_two (n : Nat) (t : Fin (cup2CycleLen n)) (j : Fin n)
    (h : j.1 = 0 ∨ j.1 + 1 = n) :
    cup2CycleVal n t.1 j.1 < 2 := by
  rcases h with h0 | htop
  · rw [h0]
    unfold cup2CycleVal cup2CycleLen
    repeat' (first | split_ifs with h | simp_all)
    omega
  · have hj : j.1 = n - 1 := by
      omega
    rw [hj]
    unfold cup2CycleVal cup2CycleLen
    repeat' (first | split_ifs with h | simp_all)

lemma cup2CycleMoverVal_lt (n : Nat) {t : Nat} (ht : t < cup2CycleLen n) :
    cup2CycleMoverVal n t < n := by
  unfold cup2CycleMoverVal cup2CycleLen at *
  split_ifs <;> omega

lemma lt_cup2CycleLen_of_lt_n (n : Nat) (hn : 4 ≤ n) {t : Nat} (ht : t < n) :
    t < cup2CycleLen n := by
  unfold cup2CycleLen
  omega

lemma lt_cup2CycleLen_of_phase1_succ (n : Nat) (hn : 4 ≤ n) {t : Nat} (ht : t < n) :
    t + 1 < cup2CycleLen n := by
  unfold cup2CycleLen
  omega

lemma lt_cup2CycleLen_of_phase2 (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (_htn : n ≤ t) (ht : t < 2 * n - 2) :
    t < cup2CycleLen n := by
  unfold cup2CycleLen
  omega

lemma lt_cup2CycleLen_of_phase2_succ (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (_htn : n ≤ t) (ht : t < 2 * n - 2) :
    t + 1 < cup2CycleLen n := by
  unfold cup2CycleLen
  omega

lemma lt_cup2CycleLen_of_phase3 (n : Nat) (_hn : 4 ≤ n) {t : Nat}
    (_ht0 : 2 * n - 2 ≤ t) (ht : t < cup2CycleLen n) :
    t < cup2CycleLen n := ht

lemma lt_cup2CycleLen_of_phase3_interior (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (_ht0 : 2 * n - 2 ≤ t) (ht : t < 3 * n - 3) :
    t < cup2CycleLen n := by
  unfold cup2CycleLen
  omega

lemma lt_cup2CycleLen_of_phase3_succ (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (_ht0 : 2 * n - 2 ≤ t) (ht : t < 3 * n - 3) :
    t + 1 < cup2CycleLen n := by
  unfold cup2CycleLen
  omega

lemma phase3_last_lt (n : Nat) (hn : 4 ≤ n) :
    3 * n - 3 < cup2CycleLen n := by
  unfold cup2CycleLen
  omega

lemma cup2CycleVal_lt_cup2M (n : Nat) (t : Fin (cup2CycleLen n)) (i : Fin n) :
    cup2CycleVal n t.1 i.1 < cup2M n i := by
  by_cases h : i.1 = 0 ∨ i.1 + 1 = n
  · have hlt : cup2CycleVal n t.1 i.1 < 2 := cup2CycleVal_endpoint_lt_two n t i h
    simpa [cup2M, h] using hlt
  · have hle : cup2CycleVal n t.1 i.1 ≤ 2 := cup2CycleVal_le_two n t i
    have hlt : cup2CycleVal n t.1 i.1 < 3 := by omega
    have hself : cup2M n i = 3 := cup2M_eq_three_of_notEndpoint h
    simpa [hself] using hlt

def cup2CycleConfig (n : Nat) (hn : 4 ≤ n) (t : Fin (cup2CycleLen n)) :
    Config (cup2Spec n hn) :=
  fun i => ⟨cup2CycleVal n t.1 i.1, cup2CycleVal_lt_cup2M n t i⟩

def cup2CycleMover (n : Nat) (_hn : 4 ≤ n) (t : Fin (cup2CycleLen n)) : Fin n :=
  ⟨cup2CycleMoverVal n t.1, cup2CycleMoverVal_lt n t.2⟩

def cup2CycleConfigs (n : Nat) (hn : 4 ≤ n) : List (Config (cup2Spec n hn)) :=
  List.ofFn (cup2CycleConfig n hn)

def cup2CycleNext (n : Nat) (t : Fin (cup2CycleLen n)) : Fin (cup2CycleLen n) :=
  ⟨(t.1 + 1) % cup2CycleLen n, by
    have hlen : 0 < cup2CycleLen n := by
      exact lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.succ_le_of_lt t.2)
    exact Nat.mod_lt _ hlen⟩

@[simp] theorem cup2CycleConfig_val (n : Nat) (hn : 4 ≤ n) (t : Fin (cup2CycleLen n))
    (i : Fin n) :
    (cup2CycleConfig n hn t i).1 = cup2CycleVal n t.1 i.1 := rfl

@[simp] theorem cup2CycleMover_val (n : Nat) (hn : 4 ≤ n) (t : Fin (cup2CycleLen n)) :
    (cup2CycleMover n hn t).1 = cup2CycleMoverVal n t.1 := rfl

@[simp] theorem cup2CycleConfigs_length (n : Nat) (hn : 4 ≤ n) :
    (cup2CycleConfigs n hn).length = cup2CycleLen n := by
  simp [cup2CycleConfigs, cup2CycleLen]

@[simp] theorem cup2CycleNext_val (n : Nat) (t : Fin (cup2CycleLen n)) :
    (cup2CycleNext n t).1 = (t.1 + 1) % cup2CycleLen n := rfl

@[simp] theorem cup2Trans_val (n : Nat) (hn : 4 ≤ n) (i : Fin n)
    (L : Fin (cup2M n (left i))) (S : Fin (cup2M n i)) (R : Fin (cup2M n (right i))) :
    (cup2Trans n hn i L S R).1 = cup2OutVal n i L.1 S.1 R.1 := rfl

section LookupCatalog

theorem lookup_bot_000 : TBotVal 0 0 0 = 1 := by native_decide
theorem lookup_bot_010 : TBotVal 0 1 0 = 1 := by native_decide
theorem lookup_bot_011 : TBotVal 0 1 1 = 1 := by native_decide
theorem lookup_bot_100 : TBotVal 1 0 0 = 0 := by native_decide
theorem lookup_bot_102 : TBotVal 1 0 2 = 0 := by native_decide
theorem lookup_bot_111 : TBotVal 1 1 1 = 1 := by native_decide
theorem lookup_bot_112 : TBotVal 1 1 2 = 0 := by native_decide

theorem lookup_low_000 : TLowVal 0 0 0 = 0 := by native_decide
theorem lookup_low_002 : TLowVal 0 0 2 = 0 := by native_decide
theorem lookup_low_022 : TLowVal 0 2 2 = 0 := by native_decide
theorem lookup_low_100 : TLowVal 1 0 0 = 1 := by native_decide
theorem lookup_low_110 : TLowVal 1 1 0 = 1 := by native_decide
theorem lookup_low_111 : TLowVal 1 1 1 = 1 := by native_decide
theorem lookup_low_112 : TLowVal 1 1 2 = 2 := by native_decide
theorem lookup_low_122 : TLowVal 1 2 2 = 2 := by native_decide

theorem lookup_mid_000 : TMidVal 0 0 0 = 0 := by native_decide
theorem lookup_mid_002 : TMidVal 0 0 2 = 0 := by native_decide
theorem lookup_mid_022 : TMidVal 0 2 2 = 0 := by native_decide
theorem lookup_mid_100 : TMidVal 1 0 0 = 1 := by native_decide
theorem lookup_mid_110 : TMidVal 1 1 0 = 1 := by native_decide
theorem lookup_mid_111 : TMidVal 1 1 1 = 1 := by native_decide
theorem lookup_mid_112 : TMidVal 1 1 2 = 2 := by native_decide
theorem lookup_mid_122 : TMidVal 1 2 2 = 2 := by native_decide
theorem lookup_mid_222 : TMidVal 2 2 2 = 2 := by native_decide

theorem lookup_high_000 : THighVal 0 0 0 = 0 := by native_decide
theorem lookup_high_001 : THighVal 0 0 1 = 0 := by native_decide
theorem lookup_high_021 : THighVal 0 2 1 = 0 := by native_decide
theorem lookup_high_100 : THighVal 1 0 0 = 1 := by native_decide
theorem lookup_high_110 : THighVal 1 1 0 = 1 := by native_decide
theorem lookup_high_111 : THighVal 1 1 1 = 2 := by native_decide
theorem lookup_high_121 : THighVal 1 2 1 = 2 := by native_decide
theorem lookup_high_221 : THighVal 2 2 1 = 2 := by native_decide

theorem lookup_top_000 : TTopVal 0 0 0 = 0 := by native_decide
theorem lookup_top_001 : TTopVal 0 0 1 = 0 := by native_decide
theorem lookup_top_010 : TTopVal 0 1 0 = 0 := by native_decide
theorem lookup_top_101 : TTopVal 1 0 1 = 1 := by native_decide
theorem lookup_top_111 : TTopVal 1 1 1 = 1 := by native_decide
theorem lookup_top_210 : TTopVal 2 1 0 = 1 := by native_decide
theorem lookup_top_211 : TTopVal 2 1 1 = 1 := by native_decide

end LookupCatalog

section MoverProofs

lemma cup2Cycle_phase1_next_mover (n : Nat) (hn : 4 ≤ n) {t : Nat} (ht : t < n) :
    cup2CycleVal n (t + 1) t = 1 := by
  unfold cup2CycleVal
  split_ifs <;> omega

lemma cup2Cycle_phase1_mover_self (n : Nat) {t : Nat} (ht : t < n) :
    cup2CycleVal n t t = 0 := by
  rw [cup2CycleVal_phase1 ht]
  simp

lemma cup2Cycle_phase1_one_before_mover (n : Nat) {t j : Nat} (ht : t < n) (hj : j < t) :
    cup2CycleVal n t j = 1 := by
  rw [cup2CycleVal_phase1 ht]
  simp [hj]

lemma cup2Cycle_phase1_zero_from_mover (n : Nat) {t j : Nat} (ht : t < n) (hj : t ≤ j) :
    cup2CycleVal n t j = 0 := by
  rw [cup2CycleVal_phase1 ht]
  have hnot : ¬ j < t := by
    omega
  simp [hnot]

def cup2Phase1Mover (n t : Nat) (ht : t < n) : Fin n :=
  ⟨t, ht⟩

def cup2Phase1Config (n : Nat) (hn : 4 ≤ n) (t : Nat) (ht : t < n) :
    Config (cup2Spec n hn) :=
  cup2CycleConfig n hn ⟨t, lt_cup2CycleLen_of_lt_n n hn ht⟩

lemma cup2Cycle_phase1_left_input (n : Nat) (_hn : 4 ≤ n) {t : Nat} (ht : t < n) :
    cup2CycleVal n t (left (cup2Phase1Mover n t ht)).1 = if t = 0 then 0 else 1 := by
  by_cases h0 : t = 0
  · subst t
    rw [cup2CycleVal_phase1 ht]
    have hleft : (left (cup2Phase1Mover n 0 ht)).1 = n - 1 := by
      simp [cup2Phase1Mover, left_val]
    rw [hleft]
    simp
  · have hleft : (left (cup2Phase1Mover n t ht)).1 = t - 1 := by
      simpa [cup2Phase1Mover] using
        (left_val_of_ne_zero (i := cup2Phase1Mover n t ht) h0)
    rw [hleft, cup2CycleVal_phase1 ht]
    have hlt : t - 1 < t := by
      omega
    simp [hlt, h0]

lemma cup2Cycle_phase1_right_input (n : Nat) (hn : 4 ≤ n) {t : Nat} (ht : t < n) :
    cup2CycleVal n t (right (cup2Phase1Mover n t ht)).1 = if t + 1 = n then 1 else 0 := by
  by_cases htop : t + 1 = n
  · have hright : (right (cup2Phase1Mover n t ht)).1 = 0 := by
      simpa [cup2Phase1Mover] using
        (right_val_of_top (i := cup2Phase1Mover n t ht) htop)
    rw [hright, cup2CycleVal_phase1 ht]
    have ht0 : t ≠ 0 := by
      intro hz
      subst hz
      omega
    have hpos : 0 < t := Nat.pos_of_ne_zero ht0
    simp [hpos, htop]
  · have hright : (right (cup2Phase1Mover n t ht)).1 = t + 1 := by
      simpa [cup2Phase1Mover] using
        (right_val_of_not_top (i := cup2Phase1Mover n t ht) htop)
    rw [hright, cup2CycleVal_phase1 ht]
    have hge : ¬ t + 1 < t := by
      omega
    simp [hge, htop]

lemma cup2Cycle_phase1_output (n : Nat) (hn : 4 ≤ n) {t : Nat} (ht : t < n) :
    cup2OutVal n (cup2Phase1Mover n t ht)
      (if t = 0 then 0 else 1) 0 (if t + 1 = n then 1 else 0) = 1 := by
  by_cases h0 : t = 0
  · subst t
    have hne : ¬ 1 = n := by
      omega
    simpa [cup2OutVal, cup2Phase1Mover, hne] using lookup_bot_000
  · by_cases h1 : t = 1
    · subst t
      have hne : ¬ 2 = n := by
        omega
      simpa [cup2OutVal, cup2Phase1Mover, h0, hne] using lookup_low_100
    · by_cases htop : t + 1 = n
      · have hhigh : t + 2 ≠ n := by
          omega
        simpa [cup2OutVal, cup2Phase1Mover, h0, h1, htop, hhigh] using lookup_top_101
      · by_cases hhigh : t + 2 = n
        · simpa [cup2OutVal, cup2Phase1Mover, h0, h1, htop, hhigh] using lookup_high_100
        · simpa [cup2OutVal, cup2Phase1Mover, h0, h1, htop, hhigh] using lookup_mid_100

lemma cup2Cycle_phase1_trans_val (n : Nat) (hn : 4 ≤ n) {t : Nat} (ht : t < n) :
    ((cup2System n hn).f (cup2Phase1Mover n t ht)
      (cup2Phase1Config n hn t ht (left (cup2Phase1Mover n t ht)))
      (cup2Phase1Config n hn t ht (cup2Phase1Mover n t ht))
      (cup2Phase1Config n hn t ht (right (cup2Phase1Mover n t ht)))).1 = 1 := by
  rw [show (cup2System n hn).f = cup2Trans n hn by rfl]
  rw [cup2Trans_val]
  have hself : cup2CycleVal n t t = 0 := cup2Cycle_phase1_mover_self n ht
  have hleft : cup2CycleVal n t ((t + n - 1) % n) = if t = 0 then 0 else 1 := by
    simpa [cup2Phase1Mover, left_val] using cup2Cycle_phase1_left_input n hn ht
  have hright : cup2CycleVal n t ((t + 1) % n) = if t + 1 = n then 1 else 0 := by
    simpa [cup2Phase1Mover, right_val] using cup2Cycle_phase1_right_input n hn ht
  simp [cup2Phase1Config, cup2Phase1Mover, hself]
  rw [hleft, hright]
  exact cup2Cycle_phase1_output n hn ht

lemma cup2Cycle_phase1_privileged (n : Nat) (hn : 4 ≤ n) {t : Nat} (ht : t < n) :
    privileged (cup2System n hn) (cup2Phase1Config n hn t ht) (cup2Phase1Mover n t ht) := by
  rw [privileged]
  intro hEq
  have hval := congrArg Fin.val hEq
  have hout :
      ((cup2System n hn).f (cup2Phase1Mover n t ht)
        (cup2Phase1Config n hn t ht (left (cup2Phase1Mover n t ht)))
        (cup2Phase1Config n hn t ht (cup2Phase1Mover n t ht))
        (cup2Phase1Config n hn t ht (right (cup2Phase1Mover n t ht)))).1 = 1 :=
    cup2Cycle_phase1_trans_val n hn ht
  have hself :
      (cup2Phase1Config n hn t ht (cup2Phase1Mover n t ht)).1 = 0 := by
    simpa [cup2Phase1Config, cup2Phase1Mover] using cup2Cycle_phase1_mover_self n ht
  rw [hout, hself] at hval
  omega

lemma cup2Cycle_phase1_nonmover_trans_val (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (ht : t < n) (i : Fin n) (hi : i ≠ cup2Phase1Mover n t ht) :
    ((cup2System n hn).f i
      (cup2Phase1Config n hn t ht (left i))
      (cup2Phase1Config n hn t ht i)
      (cup2Phase1Config n hn t ht (right i))).1 =
      (cup2Phase1Config n hn t ht i).1 := by
  let cfg : Config (cup2Spec n hn) := cup2Phase1Config n hn t ht
  rw [show (cup2System n hn).f = cup2Trans n hn by rfl]
  rw [cup2Trans_val]
  change cup2OutVal n i ((cfg (left i)).1) ((cfg i).1) ((cfg (right i)).1) = (cfg i).1
  have hmover : i.1 ≠ t := by
    intro hm
    apply hi
    ext
    simpa [cup2Phase1Mover] using hm
  by_cases h0 : i.1 = 0
  · have hself : (cfg i).1 = 1 := by
      dsimp [cfg]
      change cup2CycleVal n t i.1 = 1
      rw [h0]
      exact cup2Cycle_phase1_one_before_mover n ht (by omega)
    have hleft : (cfg (left i)).1 = 0 := by
      dsimp [cfg]
      change cup2CycleVal n t (left i).1 = 0
      have hleft_idx : (left i).1 = n - 1 := by
        rw [left_val, h0, Nat.zero_add]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hleft_idx]
      exact cup2Cycle_phase1_zero_from_mover n ht (by omega)
    have hright_idx : (right i).1 = 1 := by
      have htop : i.1 + 1 ≠ n := by
        omega
      rw [right_val_of_not_top (i := i) htop, h0]
    by_cases ht1 : t = 1
    · have hright : (cfg (right i)).1 = 0 := by
        dsimp [cfg]
        change cup2CycleVal n t (right i).1 = 0
        rw [hright_idx]
        exact cup2Cycle_phase1_zero_from_mover n ht (by omega)
      rw [hleft, hself, hright]
      simpa [cup2OutVal, h0, ht1] using lookup_bot_010
    · have hright : (cfg (right i)).1 = 1 := by
        dsimp [cfg]
        change cup2CycleVal n t (right i).1 = 1
        rw [hright_idx]
        exact cup2Cycle_phase1_one_before_mover n ht (by omega)
      rw [hleft, hself, hright]
      simpa [cup2OutVal, h0, ht1] using lookup_bot_011
  · by_cases h1 : i.1 = 1
    · by_cases ht0 : t = 0
      · have hleft : (cfg (left i)).1 = 0 := by
          dsimp [cfg]
          change cup2CycleVal n t (left i).1 = 0
          have hleft_idx : (left i).1 = 0 := by
            rw [left_val_of_ne_zero (i := i) h0, h1]
          rw [hleft_idx, ht0]
          exact cup2Cycle_phase1_zero_from_mover n (t := 0) (ht := by omega) (by omega)
        have hself : (cfg i).1 = 0 := by
          dsimp [cfg]
          change cup2CycleVal n t i.1 = 0
          rw [h1, ht0]
          exact cup2Cycle_phase1_zero_from_mover n (t := 0) (ht := by omega) (by omega)
        have hright : (cfg (right i)).1 = 0 := by
          dsimp [cfg]
          change cup2CycleVal n t (right i).1 = 0
          have htop : i.1 + 1 ≠ n := by
            omega
          have hright_idx : (right i).1 = 2 := by
            rw [right_val_of_not_top (i := i) htop, h1]
          rw [hright_idx, ht0]
          exact cup2Cycle_phase1_zero_from_mover n (t := 0) (ht := by omega) (by omega)
        rw [hleft, hself, hright]
        simpa [cup2OutVal, h0, h1, ht0] using lookup_low_000
      · by_cases ht2 : t = 2
        · have hleft : (cfg (left i)).1 = 1 := by
            dsimp [cfg]
            change cup2CycleVal n t (left i).1 = 1
            have hleft_idx : (left i).1 = 0 := by
              rw [left_val_of_ne_zero (i := i) h0, h1]
            rw [hleft_idx]
            exact cup2Cycle_phase1_one_before_mover n ht (by omega)
          have hself : (cfg i).1 = 1 := by
            dsimp [cfg]
            change cup2CycleVal n t i.1 = 1
            rw [h1]
            exact cup2Cycle_phase1_one_before_mover n ht (by omega)
          have hright : (cfg (right i)).1 = 0 := by
            dsimp [cfg]
            change cup2CycleVal n t (right i).1 = 0
            have htop : i.1 + 1 ≠ n := by
              omega
            have hright_idx : (right i).1 = 2 := by
              rw [right_val_of_not_top (i := i) htop, h1]
            rw [hright_idx]
            exact cup2Cycle_phase1_zero_from_mover n ht (by omega)
          rw [hleft, hself, hright]
          simpa [cup2OutVal, h0, h1, ht2] using lookup_low_110
        · have hleft : (cfg (left i)).1 = 1 := by
            dsimp [cfg]
            change cup2CycleVal n t (left i).1 = 1
            have hleft_idx : (left i).1 = 0 := by
              rw [left_val_of_ne_zero (i := i) h0, h1]
            rw [hleft_idx]
            exact cup2Cycle_phase1_one_before_mover n ht (by omega)
          have hself : (cfg i).1 = 1 := by
            dsimp [cfg]
            change cup2CycleVal n t i.1 = 1
            rw [h1]
            exact cup2Cycle_phase1_one_before_mover n ht (by omega)
          have hright : (cfg (right i)).1 = 1 := by
            dsimp [cfg]
            change cup2CycleVal n t (right i).1 = 1
            have htop : i.1 + 1 ≠ n := by
              omega
            have hright_idx : (right i).1 = 2 := by
              rw [right_val_of_not_top (i := i) htop, h1]
            rw [hright_idx]
            exact cup2Cycle_phase1_one_before_mover n ht (by omega)
          rw [hleft, hself, hright]
          simpa [cup2OutVal, h0, h1, ht2] using lookup_low_111
    · by_cases htop : i.1 + 1 = n
      · by_cases ht0 : t = 0
        · have hleft : (cfg (left i)).1 = 0 := by
            dsimp [cfg]
            change cup2CycleVal n t (left i).1 = 0
            have hleft_idx : (left i).1 = n - 2 := by
              rw [left_val_of_ne_zero (i := i) (by omega)]
              omega
            rw [hleft_idx, ht0]
            exact cup2Cycle_phase1_zero_from_mover n (t := 0) (ht := by omega) (by omega)
          have hself : (cfg i).1 = 0 := by
            dsimp [cfg]
            change cup2CycleVal n t i.1 = 0
            rw [show i.1 = n - 1 by omega, ht0]
            exact cup2Cycle_phase1_zero_from_mover n (t := 0) (ht := by omega) (by omega)
          have hright : (cfg (right i)).1 = 0 := by
            dsimp [cfg]
            change cup2CycleVal n t (right i).1 = 0
            rw [right_val_of_top (i := i) htop, ht0]
            exact cup2Cycle_phase1_zero_from_mover n (t := 0) (ht := by omega) (by omega)
          rw [hleft, hself, hright]
          simpa [cup2OutVal, h0, h1, htop, ht0] using lookup_top_000
        · have hleft : (cfg (left i)).1 = 0 := by
            dsimp [cfg]
            change cup2CycleVal n t (left i).1 = 0
            have hleft_idx : (left i).1 = n - 2 := by
              rw [left_val_of_ne_zero (i := i) (by omega)]
              omega
            rw [hleft_idx]
            exact cup2Cycle_phase1_zero_from_mover n ht (by omega)
          have hself : (cfg i).1 = 0 := by
            dsimp [cfg]
            change cup2CycleVal n t i.1 = 0
            rw [show i.1 = n - 1 by omega]
            exact cup2Cycle_phase1_zero_from_mover n ht (by omega)
          have hright : (cfg (right i)).1 = 1 := by
            dsimp [cfg]
            change cup2CycleVal n t (right i).1 = 1
            rw [right_val_of_top (i := i) htop]
            exact cup2Cycle_phase1_one_before_mover n ht (by omega)
          rw [hleft, hself, hright]
          simpa [cup2OutVal, h0, h1, htop, ht0] using lookup_top_001
      · by_cases hhigh : i.1 + 2 = n
        · by_cases htopMover : t + 1 = n
          · have hleft : (cfg (left i)).1 = 1 := by
              dsimp [cfg]
              change cup2CycleVal n t (left i).1 = 1
              have hleft_idx : (left i).1 = n - 3 := by
                rw [left_val_of_ne_zero (i := i) (by omega)]
                omega
              rw [hleft_idx]
              exact cup2Cycle_phase1_one_before_mover n ht (by omega)
            have hself : (cfg i).1 = 1 := by
              dsimp [cfg]
              change cup2CycleVal n t i.1 = 1
              exact cup2Cycle_phase1_one_before_mover n ht (by omega)
            have hright : (cfg (right i)).1 = 0 := by
              dsimp [cfg]
              change cup2CycleVal n t (right i).1 = 0
              have hright_idx : (right i).1 = n - 1 := by
                rw [right_val_of_not_top (i := i) htop]
                omega
              rw [hright_idx]
              exact cup2Cycle_phase1_zero_from_mover n ht (by omega)
            rw [hleft, hself, hright]
            simpa [cup2OutVal, h0, h1, htop, hhigh, htopMover] using lookup_high_110
          · have hleft : (cfg (left i)).1 = 0 := by
              dsimp [cfg]
              change cup2CycleVal n t (left i).1 = 0
              have hleft_idx : (left i).1 = n - 3 := by
                rw [left_val_of_ne_zero (i := i) (by omega)]
                omega
              rw [hleft_idx]
              exact cup2Cycle_phase1_zero_from_mover n ht (by omega)
            have hself : (cfg i).1 = 0 := by
              dsimp [cfg]
              change cup2CycleVal n t i.1 = 0
              exact cup2Cycle_phase1_zero_from_mover n ht (by omega)
            have hright : (cfg (right i)).1 = 0 := by
              dsimp [cfg]
              change cup2CycleVal n t (right i).1 = 0
              have hright_idx : (right i).1 = n - 1 := by
                rw [right_val_of_not_top (i := i) htop]
                omega
              rw [hright_idx]
              exact cup2Cycle_phase1_zero_from_mover n ht (by omega)
            rw [hleft, hself, hright]
            simpa [cup2OutVal, h0, h1, htop, hhigh, htopMover] using lookup_high_000
        · by_cases hlt : i.1 < t
          · by_cases hadj : i.1 + 1 = t
            · have hleft : (cfg (left i)).1 = 1 := by
                dsimp [cfg]
                change cup2CycleVal n t (left i).1 = 1
                have hleft_idx : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
                rw [hleft_idx]
                exact cup2Cycle_phase1_one_before_mover n ht (by omega)
              have hself : (cfg i).1 = 1 := by
                dsimp [cfg]
                change cup2CycleVal n t i.1 = 1
                exact cup2Cycle_phase1_one_before_mover n ht hlt
              have hright : (cfg (right i)).1 = 0 := by
                dsimp [cfg]
                change cup2CycleVal n t (right i).1 = 0
                have hright_idx : (right i).1 = i.1 + 1 := right_val_of_not_top htop
                rw [hright_idx]
                exact cup2Cycle_phase1_zero_from_mover n ht (by omega)
              rw [hleft, hself, hright]
              simpa [cup2OutVal, h0, h1, htop, hhigh] using lookup_mid_110
            · have hleft : (cfg (left i)).1 = 1 := by
                dsimp [cfg]
                change cup2CycleVal n t (left i).1 = 1
                have hleft_idx : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
                rw [hleft_idx]
                exact cup2Cycle_phase1_one_before_mover n ht (by omega)
              have hself : (cfg i).1 = 1 := by
                dsimp [cfg]
                change cup2CycleVal n t i.1 = 1
                exact cup2Cycle_phase1_one_before_mover n ht hlt
              have hright : (cfg (right i)).1 = 1 := by
                dsimp [cfg]
                change cup2CycleVal n t (right i).1 = 1
                have hright_idx : (right i).1 = i.1 + 1 := right_val_of_not_top htop
                rw [hright_idx]
                exact cup2Cycle_phase1_one_before_mover n ht (by omega)
              rw [hleft, hself, hright]
              simpa [cup2OutVal, h0, h1, htop, hhigh] using lookup_mid_111
          · have hleft : (cfg (left i)).1 = 0 := by
              dsimp [cfg]
              change cup2CycleVal n t (left i).1 = 0
              have hleft_idx : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
              rw [hleft_idx]
              exact cup2Cycle_phase1_zero_from_mover n ht (by omega)
            have hself : (cfg i).1 = 0 := by
              dsimp [cfg]
              change cup2CycleVal n t i.1 = 0
              exact cup2Cycle_phase1_zero_from_mover n ht (by omega)
            have hright : (cfg (right i)).1 = 0 := by
              dsimp [cfg]
              change cup2CycleVal n t (right i).1 = 0
              have hright_idx : (right i).1 = i.1 + 1 := right_val_of_not_top htop
              rw [hright_idx]
              exact cup2Cycle_phase1_zero_from_mover n ht (by omega)
            rw [hleft, hself, hright]
            simpa [cup2OutVal, h0, h1, htop, hhigh] using lookup_mid_000

lemma cup2Cycle_phase1_nonmover_not_privileged (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (ht : t < n) (i : Fin n) (hi : i ≠ cup2Phase1Mover n t ht) :
    ¬ privileged (cup2System n hn) (cup2Phase1Config n hn t ht) i := by
  rw [privileged]
  intro hneq
  apply hneq
  apply Fin.ext
  exact cup2Cycle_phase1_nonmover_trans_val n hn ht i hi

lemma cup2Cycle_phase1_singlePrivileged (n : Nat) (hn : 4 ≤ n) {t : Nat} (ht : t < n) :
    ∃! i, privileged (cup2System n hn) (cup2Phase1Config n hn t ht) i := by
  refine ⟨cup2Phase1Mover n t ht, cup2Cycle_phase1_privileged n hn ht, ?_⟩
  intro i hi
  by_contra hne
  exact (cup2Cycle_phase1_nonmover_not_privileged n hn ht i hne) hi

lemma cup2Cycle_phase1_stable (n : Nat) (hn : 4 ≤ n) {t j : Nat} (ht : t < n) (hj : j < n)
    (hjt : j ≠ t) :
    cup2CycleVal n (t + 1) j = cup2CycleVal n t j := by
  unfold cup2CycleVal
  split_ifs <;> omega

lemma cup2Cycle_phase1_step (n : Nat) (hn : 4 ≤ n) {t : Nat} (ht : t < n) :
    move (cup2System n hn) (cup2Phase1Config n hn t ht) (cup2Phase1Mover n t ht) =
      cup2CycleConfig n hn ⟨t + 1, lt_cup2CycleLen_of_phase1_succ n hn ht⟩ := by
  funext i
  by_cases hi : i = cup2Phase1Mover n t ht
  · subst hi
    apply Fin.ext
    simp [move]
    rw [cup2Cycle_phase1_trans_val]
    symm
    simpa [cup2Phase1Mover] using cup2Cycle_phase1_next_mover n hn ht
  · apply Fin.ext
    simp [move, hi, cup2Phase1Config]
    symm
    exact cup2Cycle_phase1_stable n hn ht i.2 (by
      intro h
      apply hi
      ext
      simpa [cup2Phase1Mover] using h)

def cup2Phase2Mover (n t : Nat) (htn : n ≤ t) (ht : t < 2 * n - 2) : Fin n :=
  ⟨2 * n - 2 - t, by
    omega⟩

def cup2Phase2Config (n : Nat) (hn : 4 ≤ n) (t : Nat) (htn : n ≤ t) (ht : t < 2 * n - 2) :
    Config (cup2Spec n hn) :=
  cup2CycleConfig n hn ⟨t, lt_cup2CycleLen_of_phase2 n hn htn ht⟩

def cup2Phase3Mover (n t : Nat) (_ht0 : 2 * n - 2 ≤ t) (ht : t < cup2CycleLen n) : Fin n :=
  ⟨t - (2 * n - 2), by
    unfold cup2CycleLen at ht
    omega⟩

def cup2Phase3Config (n : Nat) (hn : 4 ≤ n) (t : Nat) (_ht0 : 2 * n - 2 ≤ t)
    (ht : t < cup2CycleLen n) : Config (cup2Spec n hn) :=
  cup2CycleConfig n hn ⟨t, ht⟩

def cup2Phase3StartMover (n : Nat) (hn : 4 ≤ n) : Fin n :=
  cup2Phase3Mover n (2 * n - 2) (by omega)
    (lt_cup2CycleLen_of_phase3_interior n hn (by omega) (by omega))

def cup2Phase3StartConfig (n : Nat) (hn : 4 ≤ n) : Config (cup2Spec n hn) :=
  cup2Phase3Config n hn (2 * n - 2) (by omega)
    (lt_cup2CycleLen_of_phase3_interior n hn (by omega) (by omega))

def cup2Phase3LastMover (n : Nat) (hn : 4 ≤ n) : Fin n :=
  cup2Phase3Mover n (3 * n - 3) (by omega) (phase3_last_lt n hn)

def cup2Phase3LastConfig (n : Nat) (hn : 4 ≤ n) : Config (cup2Spec n hn) :=
  cup2Phase3Config n hn (3 * n - 3) (by omega) (phase3_last_lt n hn)

lemma phase3StartNext_lt (n : Nat) (hn : 4 ≤ n) :
    2 * n - 1 < cup2CycleLen n := by
  unfold cup2CycleLen
  omega

@[simp] lemma cup2Phase2Mover_val (n t : Nat) (htn : n ≤ t) (ht : t < 2 * n - 2) :
    (cup2Phase2Mover n t htn ht).1 = 2 * n - 2 - t := rfl

@[simp] lemma cup2Phase3Mover_val (n t : Nat) (ht0 : 2 * n - 2 ≤ t) (ht : t < cup2CycleLen n) :
    (cup2Phase3Mover n t ht0 ht).1 = t - (2 * n - 2) := rfl

@[simp] lemma cup2Phase3StartMover_val (n : Nat) (hn : 4 ≤ n) :
    (cup2Phase3StartMover n hn).1 = 0 := by
  simp [cup2Phase3StartMover, cup2Phase3Mover]

@[simp] lemma cup2Phase3LastMover_val (n : Nat) (hn : 4 ≤ n) :
    (cup2Phase3LastMover n hn).1 = n - 1 := by
  simp [cup2Phase3LastMover, cup2Phase3Mover]
  omega

lemma cup2Phase2Mover_ne_zero (n t : Nat) (htn : n ≤ t) (ht : t < 2 * n - 2) :
    (cup2Phase2Mover n t htn ht).1 ≠ 0 := by
  simp [cup2Phase2Mover]
  omega

lemma cup2Phase2Mover_not_top (n t : Nat) (htn : n ≤ t) (ht : t < 2 * n - 2) :
    (cup2Phase2Mover n t htn ht).1 + 1 ≠ n := by
  simp [cup2Phase2Mover]
  omega

lemma cup2Phase2Mover_left_val (n t : Nat) (htn : n ≤ t) (ht : t < 2 * n - 2) :
    (left (cup2Phase2Mover n t htn ht)).1 = 2 * n - 3 - t := by
  rw [left_val_of_ne_zero (i := cup2Phase2Mover n t htn ht)
    (cup2Phase2Mover_ne_zero n t htn ht)]
  simp [cup2Phase2Mover]
  omega

lemma cup2Phase2Mover_right_val (n t : Nat) (htn : n ≤ t) (ht : t < 2 * n - 2) :
    (right (cup2Phase2Mover n t htn ht)).1 = 2 * n - 1 - t := by
  rw [right_val_of_not_top (i := cup2Phase2Mover n t htn ht)
    (cup2Phase2Mover_not_top n t htn ht)]
  simp [cup2Phase2Mover]
  omega

lemma cup2Cycle_phase2_next_mover (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (htn : n ≤ t) (ht : t < 2 * n - 2) :
    cup2CycleVal n (t + 1) (2 * n - 2 - t) = 2 := by
  unfold cup2CycleVal
  split_ifs <;> omega

lemma cup2Cycle_phase2_mover_self (n : Nat) {t : Nat}
    (htn : n ≤ t) (ht : t < 2 * n - 2) :
    cup2CycleVal n t (2 * n - 2 - t) = 1 := by
  have ht1 : ¬ t < n := by
    omega
  rw [cup2CycleVal_phase2 ht1 ht]
  have hlt : 2 * n - 2 - t < 2 * n - 1 - t := by
    omega
  simp [hlt]

lemma cup2Cycle_phase2_left_input (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (htn : n ≤ t) (ht : t < 2 * n - 2) :
    cup2CycleVal n t (left (cup2Phase2Mover n t htn ht)).1 = 1 := by
  have ht1 : ¬ t < n := by
    omega
  rw [cup2Phase2Mover_left_val, cup2CycleVal_phase2 ht1 ht]
  have hlt : 2 * n - 3 - t < 2 * n - 1 - t := by
    omega
  simp [hlt]

lemma cup2Cycle_phase2_right_input (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (htn : n ≤ t) (ht : t < 2 * n - 2) :
    cup2CycleVal n t (right (cup2Phase2Mover n t htn ht)).1 = if t = n then 1 else 2 := by
  have ht1 : ¬ t < n := by
    omega
  rw [cup2Phase2Mover_right_val, cup2CycleVal_phase2 ht1 ht]
  by_cases hstart : t = n
  · subst t
    have hcut : 2 * n - 1 - n = n - 1 := by
      omega
    rw [hcut]
    simp
  · have hlt : 2 * n - 1 - t < n - 1 := by
      omega
    simp [hlt, hstart]

lemma cup2Cycle_phase2_one_before_front (n : Nat) {t j : Nat}
    (htn : n ≤ t) (ht : t < 2 * n - 2) (hj : j < 2 * n - 1 - t) :
    cup2CycleVal n t j = 1 := by
  have ht1 : ¬ t < n := by
    omega
  rw [cup2CycleVal_phase2 ht1 ht]
  simp [hj]

lemma cup2Cycle_phase2_two_before_top (n : Nat) {t j : Nat}
    (htn : n ≤ t) (ht : t < 2 * n - 2)
    (hk : 2 * n - 1 - t ≤ j) (hj : j < n - 1) :
    cup2CycleVal n t j = 2 := by
  have ht1 : ¬ t < n := by
    omega
  rw [cup2CycleVal_phase2 ht1 ht]
  have hnot : ¬ j < 2 * n - 1 - t := by
    omega
  simp [hnot, hj]

lemma cup2Cycle_phase2_top_val (n : Nat) {t : Nat}
    (htn : n ≤ t) (ht : t < 2 * n - 2) :
    cup2CycleVal n t (n - 1) = 1 := by
  have ht1 : ¬ t < n := by
    omega
  rw [cup2CycleVal_phase2 ht1 ht]
  have hnot : ¬ n - 1 < 2 * n - 1 - t := by
    omega
  have hnot' : ¬ n - 1 < n - 1 := by
    omega
  simp [hnot, hnot']

lemma cup2Cycle_phase2_output (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (htn : n ≤ t) (ht : t < 2 * n - 2) :
    cup2OutVal n (cup2Phase2Mover n t htn ht) 1 1 (if t = n then 1 else 2) = 2 := by
  by_cases hstart : t = n
  · subst t
    have hm : 2 * n - 2 - n = n - 2 := by
      omega
    have h0 : ¬ n - 2 = 0 := by
      omega
    have h1 : ¬ n - 2 = 1 := by
      omega
    have htop : ¬ n - 2 + 1 = n := by
      omega
    have hhigh : n - 2 + 2 = n := by
      omega
    simpa [cup2OutVal, cup2Phase2Mover, hm, h0, h1, htop, hhigh] using lookup_high_111
  · by_cases hlow : t = 2 * n - 3
    · subst t
      have hm : 2 * n - 2 - (2 * n - 3) = 1 := by
        omega
      have h0 : ¬ (1 : Nat) = 0 := by
        decide
      simpa [cup2OutVal, cup2Phase2Mover, hm, h0, hstart] using lookup_low_112
    · have h0 : ¬ 2 * n - 2 - t = 0 := by
        omega
      have h1 : ¬ 2 * n - 2 - t = 1 := by
        omega
      have htop : ¬ (2 * n - 2 - t) + 1 = n := by
        omega
      have hhigh : ¬ (2 * n - 2 - t) + 2 = n := by
        omega
      simpa [cup2OutVal, cup2Phase2Mover, h0, h1, htop, hhigh, hstart] using lookup_mid_112

lemma cup2Cycle_phase2_trans_val (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (htn : n ≤ t) (ht : t < 2 * n - 2) :
    ((cup2System n hn).f (cup2Phase2Mover n t htn ht)
      (cup2Phase2Config n hn t htn ht (left (cup2Phase2Mover n t htn ht)))
      (cup2Phase2Config n hn t htn ht (cup2Phase2Mover n t htn ht))
      (cup2Phase2Config n hn t htn ht (right (cup2Phase2Mover n t htn ht)))).1 = 2 := by
  rw [show (cup2System n hn).f = cup2Trans n hn by rfl]
  rw [cup2Trans_val]
  have hleft : cup2CycleVal n t ((2 * n - 2 - t + n - 1) % n) = 1 := by
    simpa [cup2Phase2Mover, left_val] using cup2Cycle_phase2_left_input n hn htn ht
  have hself : cup2CycleVal n t (2 * n - 2 - t) = 1 := cup2Cycle_phase2_mover_self n htn ht
  have hright : cup2CycleVal n t ((2 * n - 2 - t + 1) % n) = if t = n then 1 else 2 := by
    simpa [cup2Phase2Mover, right_val] using cup2Cycle_phase2_right_input n hn htn ht
  simp [cup2Phase2Config, hself]
  rw [hleft, hright]
  exact cup2Cycle_phase2_output n hn htn ht

lemma cup2Cycle_phase2_privileged (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (htn : n ≤ t) (ht : t < 2 * n - 2) :
    privileged (cup2System n hn) (cup2Phase2Config n hn t htn ht) (cup2Phase2Mover n t htn ht) := by
  rw [privileged]
  intro hEq
  have hval := congrArg Fin.val hEq
  have hout :
      ((cup2System n hn).f (cup2Phase2Mover n t htn ht)
        (cup2Phase2Config n hn t htn ht (left (cup2Phase2Mover n t htn ht)))
        (cup2Phase2Config n hn t htn ht (cup2Phase2Mover n t htn ht))
        (cup2Phase2Config n hn t htn ht (right (cup2Phase2Mover n t htn ht)))).1 = 2 :=
    cup2Cycle_phase2_trans_val n hn htn ht
  have hself :
      (cup2Phase2Config n hn t htn ht (cup2Phase2Mover n t htn ht)).1 = 1 := by
    simpa [cup2Phase2Config, cup2Phase2Mover] using cup2Cycle_phase2_mover_self n htn ht
  rw [hout, hself] at hval
  omega

lemma cup2Cycle_phase2_nonmover_trans_val (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (htn : n ≤ t) (ht : t < 2 * n - 2) (i : Fin n)
    (hi : i ≠ cup2Phase2Mover n t htn ht) :
    ((cup2System n hn).f i
      (cup2Phase2Config n hn t htn ht (left i))
      (cup2Phase2Config n hn t htn ht i)
      (cup2Phase2Config n hn t htn ht (right i))).1 =
      (cup2Phase2Config n hn t htn ht i).1 := by
  let cfg : Config (cup2Spec n hn) := cup2Phase2Config n hn t htn ht
  rw [show (cup2System n hn).f = cup2Trans n hn by rfl]
  rw [cup2Trans_val]
  change cup2OutVal n i ((cfg (left i)).1) ((cfg i).1) ((cfg (right i)).1) = (cfg i).1
  have hmover : i.1 ≠ 2 * n - 2 - t := by
    intro hm
    apply hi
    ext
    simpa [cup2Phase2Mover] using hm
  by_cases h0 : i.1 = 0
  · have hleft : (cfg (left i)).1 = 1 := by
      dsimp [cfg]
      change cup2CycleVal n t (left i).1 = 1
      have hleft_idx : (left i).1 = n - 1 := by
        rw [left_val, h0, Nat.zero_add]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hleft_idx]
      simpa using cup2Cycle_phase2_top_val n htn ht
    have hself : (cfg i).1 = 1 := by
      dsimp [cfg]
      change cup2CycleVal n t i.1 = 1
      rw [h0]
      exact cup2Cycle_phase2_one_before_front n htn ht (by omega)
    have hright : (cfg (right i)).1 = 1 := by
      dsimp [cfg]
      change cup2CycleVal n t (right i).1 = 1
      have htop : i.1 + 1 ≠ n := by
        omega
      have hright_idx : (right i).1 = 1 := by
        rw [right_val_of_not_top (i := i) htop, h0]
      rw [hright_idx]
      exact cup2Cycle_phase2_one_before_front n htn ht (by omega)
    rw [hleft, hself, hright]
    simpa [cup2OutVal, h0] using lookup_bot_111
  · by_cases h1 : i.1 = 1
    · have hleft : (cfg (left i)).1 = 1 := by
        dsimp [cfg]
        change cup2CycleVal n t (left i).1 = 1
        have hleft_idx : (left i).1 = 0 := by
          rw [left_val_of_ne_zero (i := i) h0, h1]
        rw [hleft_idx]
        exact cup2Cycle_phase2_one_before_front n htn ht (by omega)
      have hself : (cfg i).1 = 1 := by
        dsimp [cfg]
        change cup2CycleVal n t i.1 = 1
        rw [h1]
        exact cup2Cycle_phase2_one_before_front n htn ht (by omega)
      have hright : (cfg (right i)).1 = 1 := by
        dsimp [cfg]
        change cup2CycleVal n t (right i).1 = 1
        have htop : i.1 + 1 ≠ n := by
          omega
        have hright_idx : (right i).1 = 2 := by
          rw [right_val_of_not_top (i := i) htop, h1]
        rw [hright_idx]
        exact cup2Cycle_phase2_one_before_front n htn ht (by omega)
      rw [hleft, hself, hright]
      simpa [cup2OutVal, h0, h1] using lookup_low_111
    · by_cases htop : i.1 + 1 = n
      · have hself : (cfg i).1 = 1 := by
          dsimp [cfg]
          change cup2CycleVal n t i.1 = 1
          rw [show i.1 = n - 1 by omega]
          simpa using cup2Cycle_phase2_top_val n htn ht
        have hright : (cfg (right i)).1 = 1 := by
          dsimp [cfg]
          change cup2CycleVal n t (right i).1 = 1
          rw [right_val_of_top (i := i) htop]
          exact cup2Cycle_phase2_one_before_front n htn ht (by omega)
        by_cases hstart : t = n
        · have hleft : (cfg (left i)).1 = 1 := by
            dsimp [cfg]
            change cup2CycleVal n t (left i).1 = 1
            have hleft_idx : (left i).1 = n - 2 := by
              rw [left_val_of_ne_zero (i := i) (by omega)]
              omega
            rw [hleft_idx]
            exact cup2Cycle_phase2_one_before_front n htn ht (by omega)
          rw [hleft, hself, hright]
          simpa [cup2OutVal, h0, h1, htop, hstart] using lookup_top_111
        · have hleft : (cfg (left i)).1 = 2 := by
            dsimp [cfg]
            change cup2CycleVal n t (left i).1 = 2
            have hleft_idx : (left i).1 = n - 2 := by
              rw [left_val_of_ne_zero (i := i) (by omega)]
              omega
            rw [hleft_idx]
            exact cup2Cycle_phase2_two_before_top n htn ht (by omega) (by omega)
          rw [hleft, hself, hright]
          simpa [cup2OutVal, h0, h1, htop, hstart] using lookup_top_211
      · by_cases hhigh : i.1 + 2 = n
        · have hself : (cfg i).1 = 2 := by
            dsimp [cfg]
            change cup2CycleVal n t i.1 = 2
            exact cup2Cycle_phase2_two_before_top n htn ht (by omega) (by omega)
          have hright : (cfg (right i)).1 = 1 := by
            dsimp [cfg]
            change cup2CycleVal n t (right i).1 = 1
            have hright_idx : (right i).1 = n - 1 := by
              rw [right_val_of_not_top (i := i) htop]
              omega
            rw [hright_idx]
            simpa using cup2Cycle_phase2_top_val n htn ht
          by_cases hfront : 2 * n - 1 - t = n - 2
          · have hleft : (cfg (left i)).1 = 1 := by
              dsimp [cfg]
              change cup2CycleVal n t (left i).1 = 1
              have hleft_idx : (left i).1 = n - 3 := by
                rw [left_val_of_ne_zero (i := i) (by omega)]
                omega
              rw [hleft_idx]
              exact cup2Cycle_phase2_one_before_front n htn ht (by omega)
            rw [hleft, hself, hright]
            simpa [cup2OutVal, h0, h1, htop, hhigh, hfront] using lookup_high_121
          · have hleft : (cfg (left i)).1 = 2 := by
              dsimp [cfg]
              change cup2CycleVal n t (left i).1 = 2
              have hleft_idx : (left i).1 = n - 3 := by
                rw [left_val_of_ne_zero (i := i) (by omega)]
                omega
              rw [hleft_idx]
              exact cup2Cycle_phase2_two_before_top n htn ht (by omega) (by omega)
            rw [hleft, hself, hright]
            simpa [cup2OutVal, h0, h1, htop, hhigh, hfront] using lookup_high_221
        · by_cases hfrontEq : i.1 = 2 * n - 1 - t
          · have hleft : (cfg (left i)).1 = 1 := by
              dsimp [cfg]
              change cup2CycleVal n t (left i).1 = 1
              have hleft_idx : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
              rw [hleft_idx]
              exact cup2Cycle_phase2_one_before_front n htn ht (by omega)
            have hself : (cfg i).1 = 2 := by
              dsimp [cfg]
              change cup2CycleVal n t i.1 = 2
              exact cup2Cycle_phase2_two_before_top n htn ht (by omega) (by omega)
            have hright : (cfg (right i)).1 = 2 := by
              dsimp [cfg]
              change cup2CycleVal n t (right i).1 = 2
              have hright_idx : (right i).1 = i.1 + 1 := right_val_of_not_top htop
              rw [hright_idx]
              exact cup2Cycle_phase2_two_before_top n htn ht (by omega) (by omega)
            rw [hleft, hself, hright]
            simpa [cup2OutVal, h0, h1, htop, hhigh] using lookup_mid_122
          · by_cases hlt : i.1 < 2 * n - 1 - t
            · have hleft : (cfg (left i)).1 = 1 := by
                dsimp [cfg]
                change cup2CycleVal n t (left i).1 = 1
                have hleft_idx : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
                rw [hleft_idx]
                exact cup2Cycle_phase2_one_before_front n htn ht (by omega)
              have hself : (cfg i).1 = 1 := by
                dsimp [cfg]
                change cup2CycleVal n t i.1 = 1
                exact cup2Cycle_phase2_one_before_front n htn ht hlt
              have hright : (cfg (right i)).1 = 1 := by
                dsimp [cfg]
                change cup2CycleVal n t (right i).1 = 1
                have hright_idx : (right i).1 = i.1 + 1 := right_val_of_not_top htop
                rw [hright_idx]
                exact cup2Cycle_phase2_one_before_front n htn ht (by omega)
              rw [hleft, hself, hright]
              simpa [cup2OutVal, h0, h1, htop, hhigh] using lookup_mid_111
            · have hleft : (cfg (left i)).1 = 2 := by
                dsimp [cfg]
                change cup2CycleVal n t (left i).1 = 2
                have hleft_idx : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
                rw [hleft_idx]
                exact cup2Cycle_phase2_two_before_top n htn ht (by omega) (by omega)
              have hself : (cfg i).1 = 2 := by
                dsimp [cfg]
                change cup2CycleVal n t i.1 = 2
                exact cup2Cycle_phase2_two_before_top n htn ht (by omega) (by omega)
              have hright : (cfg (right i)).1 = 2 := by
                dsimp [cfg]
                change cup2CycleVal n t (right i).1 = 2
                have hright_idx : (right i).1 = i.1 + 1 := right_val_of_not_top htop
                rw [hright_idx]
                exact cup2Cycle_phase2_two_before_top n htn ht (by omega) (by omega)
              rw [hleft, hself, hright]
              simpa [cup2OutVal, h0, h1, htop, hhigh] using lookup_mid_222

lemma cup2Cycle_phase2_nonmover_not_privileged (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (htn : n ≤ t) (ht : t < 2 * n - 2) (i : Fin n)
    (hi : i ≠ cup2Phase2Mover n t htn ht) :
    ¬ privileged (cup2System n hn) (cup2Phase2Config n hn t htn ht) i := by
  rw [privileged]
  intro hneq
  apply hneq
  apply Fin.ext
  exact cup2Cycle_phase2_nonmover_trans_val n hn htn ht i hi

lemma cup2Cycle_phase2_singlePrivileged (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (htn : n ≤ t) (ht : t < 2 * n - 2) :
    ∃! i, privileged (cup2System n hn) (cup2Phase2Config n hn t htn ht) i := by
  refine ⟨cup2Phase2Mover n t htn ht, cup2Cycle_phase2_privileged n hn htn ht, ?_⟩
  intro i hi
  by_contra hne
  exact (cup2Cycle_phase2_nonmover_not_privileged n hn htn ht i hne) hi

lemma cup2Cycle_phase2_stable (n : Nat) (hn : 4 ≤ n) {t j : Nat}
    (htn : n ≤ t) (ht : t < 2 * n - 2) (hj : j < n)
    (hjt : j ≠ 2 * n - 2 - t) :
    cup2CycleVal n (t + 1) j = cup2CycleVal n t j := by
  unfold cup2CycleVal
  split_ifs <;> omega

lemma cup2Cycle_phase2_step (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (htn : n ≤ t) (ht : t < 2 * n - 2) :
    move (cup2System n hn) (cup2Phase2Config n hn t htn ht) (cup2Phase2Mover n t htn ht) =
      cup2CycleConfig n hn ⟨t + 1, lt_cup2CycleLen_of_phase2_succ n hn htn ht⟩ := by
  funext i
  by_cases hi : i = cup2Phase2Mover n t htn ht
  · subst hi
    apply Fin.ext
    simp [move]
    rw [cup2Cycle_phase2_trans_val]
    symm
    simpa [cup2Phase2Mover] using cup2Cycle_phase2_next_mover n hn htn ht
  · apply Fin.ext
    simp [move, hi, cup2Phase2Config]
    symm
    exact cup2Cycle_phase2_stable n hn htn ht i.2 (by
      intro h
      apply hi
      ext
      simpa [cup2Phase2Mover] using h)

lemma cup2Cycle_phase3_start_self (n : Nat) (hn : 4 ≤ n) :
    cup2CycleVal n (2 * n - 2) 0 = 1 := by
  have ht1 : ¬ 2 * n - 2 < n := by
    omega
  have ht2 : ¬ 2 * n - 2 < 2 * n - 2 := by
    omega
  rw [cup2CycleVal_phase3_boundary ht1 ht2 rfl]
  simp

lemma cup2Cycle_phase3_start_next (n : Nat) (hn : 4 ≤ n) :
    cup2CycleVal n (2 * n - 1) 0 = 0 := by
  have ht1 : ¬ 2 * n - 1 < n := by
    omega
  have ht2 : ¬ 2 * n - 1 < 2 * n - 2 := by
    omega
  have hboundary : 2 * n - 1 ≠ 2 * n - 2 := by
    omega
  rw [cup2CycleVal_phase3 ht1 ht2 hboundary]
  have hcut : 2 * n - 1 - (2 * n - 2) = 1 := by
    omega
  rw [hcut]
  simp

lemma cup2Cycle_phase3_start_left_input (n : Nat) (hn : 4 ≤ n) :
    cup2CycleVal n (2 * n - 2) (n - 1) = 1 := by
  have ht1 : ¬ 2 * n - 2 < n := by
    omega
  have ht2 : ¬ 2 * n - 2 < 2 * n - 2 := by
    omega
  rw [cup2CycleVal_phase3_boundary ht1 ht2 rfl]
  have hnot : ¬ n - 1 = 0 := by
    omega
  simp [hnot]

lemma cup2Cycle_phase3_start_right_input (n : Nat) (hn : 4 ≤ n) :
    cup2CycleVal n (2 * n - 2) 1 = 2 := by
  have ht1 : ¬ 2 * n - 2 < n := by
    omega
  have ht2 : ¬ 2 * n - 2 < 2 * n - 2 := by
    omega
  rw [cup2CycleVal_phase3_boundary ht1 ht2 rfl]
  have h2 : 1 < n - 1 := by
    omega
  simp [h2]

lemma cup2Cycle_phase3_start_two_before_top (n : Nat) (hn : 4 ≤ n) {j : Nat}
    (hj0 : j ≠ 0) (hj : j < n - 1) :
    cup2CycleVal n (2 * n - 2) j = 2 := by
  have ht1 : ¬ 2 * n - 2 < n := by
    omega
  have ht2 : ¬ 2 * n - 2 < 2 * n - 2 := by
    omega
  rw [cup2CycleVal_phase3_boundary ht1 ht2 rfl]
  simp [hj0, hj]

lemma cup2Cycle_phase3_start_output (n : Nat) (hn : 4 ≤ n) :
    cup2OutVal n (cup2Phase3StartMover n hn) 1 1 2 = 0 := by
  simpa [cup2OutVal, cup2Phase3StartMover_val n hn] using lookup_bot_112

lemma cup2Cycle_phase3_start_trans_val (n : Nat) (hn : 4 ≤ n) :
    ((cup2System n hn).f (cup2Phase3StartMover n hn)
      (cup2Phase3StartConfig n hn (left (cup2Phase3StartMover n hn)))
      (cup2Phase3StartConfig n hn (cup2Phase3StartMover n hn))
      (cup2Phase3StartConfig n hn (right (cup2Phase3StartMover n hn)))).1 = 0 := by
  rw [show (cup2System n hn).f = cup2Trans n hn by rfl]
  rw [cup2Trans_val]
  simp [cup2Phase3StartConfig, cup2Phase3Config]
  have h1lt : 1 < n := by
    omega
  rw [Nat.mod_eq_of_lt h1lt]
  rw [cup2Cycle_phase3_start_left_input n hn, cup2Cycle_phase3_start_self n hn,
    cup2Cycle_phase3_start_right_input n hn]
  exact cup2Cycle_phase3_start_output n hn

lemma cup2Cycle_phase3_start_privileged (n : Nat) (hn : 4 ≤ n) :
    privileged (cup2System n hn) (cup2Phase3StartConfig n hn) (cup2Phase3StartMover n hn) := by
  rw [privileged]
  intro hEq
  have hval := congrArg Fin.val hEq
  have hout :
      ((cup2System n hn).f (cup2Phase3StartMover n hn)
        (cup2Phase3StartConfig n hn (left (cup2Phase3StartMover n hn)))
        (cup2Phase3StartConfig n hn (cup2Phase3StartMover n hn))
        (cup2Phase3StartConfig n hn (right (cup2Phase3StartMover n hn)))).1 = 0 :=
    cup2Cycle_phase3_start_trans_val n hn
  have hself :
      (cup2Phase3StartConfig n hn (cup2Phase3StartMover n hn)).1 = 1 := by
    simpa [cup2Phase3StartConfig, cup2Phase3Config, cup2Phase3StartMover, cup2Phase3Mover] using
      cup2Cycle_phase3_start_self n hn
  rw [hout, hself] at hval
  omega

lemma cup2Cycle_phase3_start_nonmover_trans_val (n : Nat) (hn : 4 ≤ n) (i : Fin n)
    (hi : i ≠ cup2Phase3StartMover n hn) :
    ((cup2System n hn).f i
      (cup2Phase3StartConfig n hn (left i))
      (cup2Phase3StartConfig n hn i)
      (cup2Phase3StartConfig n hn (right i))).1 =
      (cup2Phase3StartConfig n hn i).1 := by
  rw [show (cup2System n hn).f = cup2Trans n hn by rfl]
  rw [cup2Trans_val]
  have h0 : i.1 ≠ 0 := by
    intro hi0
    apply hi
    ext
    rw [cup2Phase3StartMover_val n hn]
    exact hi0
  by_cases h1 : i.1 = 1
  · have hleft : (cup2Phase3StartConfig n hn (left i)).1 = 1 := by
      change cup2CycleVal n (2 * n - 2) (left i).1 = 1
      have hleft_idx : (left i).1 = 0 := by
        rw [left_val_of_ne_zero (i := i) h0, h1]
      rw [hleft_idx]
      simpa using cup2Cycle_phase3_start_self n hn
    have hself : (cup2Phase3StartConfig n hn i).1 = 2 := by
      change cup2CycleVal n (2 * n - 2) i.1 = 2
      rw [h1]
      simpa using cup2Cycle_phase3_start_two_before_top n hn (j := 1) (by omega) (by omega)
    have hright : (cup2Phase3StartConfig n hn (right i)).1 = 2 := by
      change cup2CycleVal n (2 * n - 2) (right i).1 = 2
      have htop : i.1 + 1 ≠ n := by
        omega
      have hright_idx : (right i).1 = 2 := by
        rw [right_val_of_not_top (i := i) htop, h1]
      rw [hright_idx]
      simpa using cup2Cycle_phase3_start_two_before_top n hn (j := 2) (by omega) (by omega)
    rw [hleft, hself, hright]
    simpa [cup2OutVal, h0, h1] using lookup_low_122
  · by_cases htop : i.1 + 1 = n
    · have hleft : (cup2Phase3StartConfig n hn (left i)).1 = 2 := by
        change cup2CycleVal n (2 * n - 2) (left i).1 = 2
        have hleft_idx : (left i).1 = n - 2 := by
          rw [left_val_of_ne_zero (i := i) h0]
          omega
        rw [hleft_idx]
        simpa using cup2Cycle_phase3_start_two_before_top n hn (j := n - 2) (by omega) (by omega)
      have hself : (cup2Phase3StartConfig n hn i).1 = 1 := by
        change cup2CycleVal n (2 * n - 2) i.1 = 1
        rw [show i.1 = n - 1 by omega]
        simpa using cup2Cycle_phase3_start_left_input n hn
      have hright : (cup2Phase3StartConfig n hn (right i)).1 = 1 := by
        change cup2CycleVal n (2 * n - 2) (right i).1 = 1
        rw [right_val_of_top (i := i) htop]
        simpa using cup2Cycle_phase3_start_self n hn
      rw [hleft, hself, hright]
      simpa [cup2OutVal, h0, h1, htop] using lookup_top_211
    · by_cases hhigh : i.1 + 2 = n
      · have hleft : (cup2Phase3StartConfig n hn (left i)).1 = 2 := by
          change cup2CycleVal n (2 * n - 2) (left i).1 = 2
          have hleft_idx : (left i).1 = n - 3 := by
            rw [left_val_of_ne_zero (i := i) h0]
            omega
          rw [hleft_idx]
          simpa using cup2Cycle_phase3_start_two_before_top n hn (j := n - 3) (by omega) (by omega)
        have hself : (cup2Phase3StartConfig n hn i).1 = 2 := by
          change cup2CycleVal n (2 * n - 2) i.1 = 2
          have hi_idx : i.1 = n - 2 := by
            omega
          rw [hi_idx]
          simpa using cup2Cycle_phase3_start_two_before_top n hn (j := n - 2) (by omega) (by omega)
        have hright : (cup2Phase3StartConfig n hn (right i)).1 = 1 := by
          change cup2CycleVal n (2 * n - 2) (right i).1 = 1
          have hright_idx : (right i).1 = n - 1 := by
            rw [right_val_of_not_top (i := i) htop]
            omega
          rw [hright_idx]
          simpa using cup2Cycle_phase3_start_left_input n hn
        rw [hleft, hself, hright]
        simpa [cup2OutVal, h0, h1, htop, hhigh] using lookup_high_221
      · have hleft : (cup2Phase3StartConfig n hn (left i)).1 = 2 := by
          change cup2CycleVal n (2 * n - 2) (left i).1 = 2
          have hleft_idx : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
          rw [hleft_idx]
          have hleft_nz : i.1 - 1 ≠ 0 := by
            omega
          have hleft_lt : i.1 - 1 < n - 1 := by
            omega
          simpa using cup2Cycle_phase3_start_two_before_top n hn (j := i.1 - 1) hleft_nz hleft_lt
        have hself : (cup2Phase3StartConfig n hn i).1 = 2 := by
          change cup2CycleVal n (2 * n - 2) i.1 = 2
          have hi_lt : i.1 < n - 1 := by
            omega
          simpa using cup2Cycle_phase3_start_two_before_top n hn (j := i.1) h0 hi_lt
        have hright : (cup2Phase3StartConfig n hn (right i)).1 = 2 := by
          change cup2CycleVal n (2 * n - 2) (right i).1 = 2
          have hright_idx : (right i).1 = i.1 + 1 := right_val_of_not_top htop
          rw [hright_idx]
          have hright_nz : i.1 + 1 ≠ 0 := by
            omega
          have hright_lt : i.1 + 1 < n - 1 := by
            omega
          simpa using cup2Cycle_phase3_start_two_before_top n hn (j := i.1 + 1) hright_nz hright_lt
        rw [hleft, hself, hright]
        simpa [cup2OutVal, h0, h1, htop, hhigh] using lookup_mid_222

lemma cup2Cycle_phase3_start_nonmover_not_privileged (n : Nat) (hn : 4 ≤ n) (i : Fin n)
    (hi : i ≠ cup2Phase3StartMover n hn) :
    ¬ privileged (cup2System n hn) (cup2Phase3StartConfig n hn) i := by
  rw [privileged]
  intro hneq
  apply hneq
  apply Fin.ext
  exact cup2Cycle_phase3_start_nonmover_trans_val n hn i hi

lemma cup2Cycle_phase3_start_singlePrivileged (n : Nat) (hn : 4 ≤ n) :
    ∃! i, privileged (cup2System n hn) (cup2Phase3StartConfig n hn) i := by
  refine ⟨cup2Phase3StartMover n hn, cup2Cycle_phase3_start_privileged n hn, ?_⟩
  intro i hi
  by_contra hne
  exact (cup2Cycle_phase3_start_nonmover_not_privileged n hn i hne) hi

lemma cup2Cycle_phase3_start_stable (n : Nat) (hn : 4 ≤ n) {j : Nat} (_hj : j < n)
    (hj0 : j ≠ 0) :
    cup2CycleVal n (2 * n - 1) j = cup2CycleVal n (2 * n - 2) j := by
  have hs1 : ¬ 2 * n - 2 < n := by
    omega
  have hs2 : ¬ 2 * n - 2 < 2 * n - 2 := by
    omega
  have ht1 : ¬ 2 * n - 1 < n := by
    omega
  have ht2 : ¬ 2 * n - 1 < 2 * n - 2 := by
    omega
  have hboundary : 2 * n - 1 ≠ 2 * n - 2 := by
    omega
  rw [cup2CycleVal_phase3 ht1 ht2 hboundary, cup2CycleVal_phase3_boundary hs1 hs2 rfl]
  have hk : 2 * n - 1 - (2 * n - 2) = 1 := by
    omega
  rw [hk]
  have hj1 : ¬ j < 1 := by
    omega
  simp [hj1, hj0]

lemma cup2Cycle_phase3_start_step (n : Nat) (hn : 4 ≤ n) :
    move (cup2System n hn) (cup2Phase3StartConfig n hn) (cup2Phase3StartMover n hn) =
      cup2CycleConfig n hn ⟨2 * n - 1, phase3StartNext_lt n hn⟩ := by
  funext i
  by_cases hi : i = cup2Phase3StartMover n hn
  · subst hi
    apply Fin.ext
    simp [move]
    rw [cup2Cycle_phase3_start_trans_val]
    symm
    simpa [cup2Phase3StartMover, cup2Phase3Mover] using cup2Cycle_phase3_start_next n hn
  · apply Fin.ext
    simp [move, hi, cup2Phase3StartConfig, cup2Phase3Config]
    symm
    exact cup2Cycle_phase3_start_stable n hn i.2 (by
      intro h
      apply hi
      ext
      simpa [cup2Phase3StartMover, cup2Phase3Mover] using h)

lemma cup2Cycle_phase3_nonstart_val (n : Nat) {t j : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < 3 * n - 3) :
    cup2CycleVal n t j =
      if j < t - (2 * n - 2) then 0 else if j < n - 1 then 2 else 1 := by
  have ht1 : ¬ t < n := by
    omega
  have ht2 : ¬ t < 2 * n - 2 := by
    omega
  have hboundary : t ≠ 2 * n - 2 := by
    omega
  rw [cup2CycleVal_phase3 ht1 ht2 hboundary]
  have hk : t - (2 * n - 2) ≠ 0 := by
    omega
  simp [hk]

lemma cup2Cycle_phase3_nonstart_zero_before_mover (n : Nat) {t j : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < 3 * n - 3) (hj : j < t - (2 * n - 2)) :
    cup2CycleVal n t j = 0 := by
  rw [cup2Cycle_phase3_nonstart_val n ht0 ht]
  simp [hj]

lemma cup2Cycle_phase3_nonstart_two_before_top (n : Nat) {t j : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < 3 * n - 3)
    (hk : t - (2 * n - 2) ≤ j) (hj : j < n - 1) :
    cup2CycleVal n t j = 2 := by
  rw [cup2Cycle_phase3_nonstart_val n ht0 ht]
  have hnot : ¬ j < t - (2 * n - 2) := by
    omega
  simp [hnot, hj]

lemma cup2Cycle_phase3_nonstart_top_val (n : Nat) {t : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < 3 * n - 3) :
    cup2CycleVal n t (n - 1) = 1 := by
  rw [cup2Cycle_phase3_nonstart_val n ht0 ht]
  have hnot : ¬ n - 1 < t - (2 * n - 2) := by
    omega
  have hnot' : ¬ n - 1 < n - 1 := by
    omega
  simp [hnot, hnot']

lemma cup2Cycle_phase3_nonstart_self (n : Nat) {t : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < 3 * n - 3) :
    cup2CycleVal n t (t - (2 * n - 2)) = 2 := by
  exact cup2Cycle_phase3_nonstart_two_before_top n ht0 ht (by omega) (by omega)

lemma cup2Cycle_phase3_nonstart_next (n : Nat) (_hn : 4 ≤ n) {t : Nat}
    (ht0 : 2 * n - 1 ≤ t) (_ht : t < 3 * n - 3) :
    cup2CycleVal n (t + 1) (t - (2 * n - 2)) = 0 := by
  have ht1 : ¬ t + 1 < n := by
    omega
  have ht2 : ¬ t + 1 < 2 * n - 2 := by
    omega
  have hboundary : t + 1 ≠ 2 * n - 2 := by
    omega
  rw [cup2CycleVal_phase3 ht1 ht2 hboundary]
  have hk : t + 1 - (2 * n - 2) ≠ 0 := by
    omega
  have hlt : t - (2 * n - 2) < t + 1 - (2 * n - 2) := by
    omega
  simp [hk, hlt]

lemma cup2Phase3Mover_nonstart_ne_zero (n : Nat) {t : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < cup2CycleLen n) :
    (cup2Phase3Mover n t (by omega) ht).1 ≠ 0 := by
  have hn : 1 ≤ n := by
    unfold cup2CycleLen at ht
    omega
  change t - (2 * n - 2) ≠ 0
  omega

lemma cup2Phase3Mover_nonstart_not_top (n : Nat) {t : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < 3 * n - 3) :
    (cup2Phase3Mover n t (by omega)
      (by
        unfold cup2CycleLen
        omega)).1 + 1 ≠ n := by
  change t - (2 * n - 2) + 1 ≠ n
  omega

lemma cup2Phase3Mover_nonstart_left_val (n : Nat) {t : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < 3 * n - 3) :
    (left (cup2Phase3Mover n t (by omega)
      (by
        unfold cup2CycleLen
        omega))).1 =
      t - (2 * n - 2) - 1 := by
  rw [left_val_of_ne_zero (i := cup2Phase3Mover n t (by omega)
    (by
      unfold cup2CycleLen
      omega))
    (cup2Phase3Mover_nonstart_ne_zero n ht0 (by
      unfold cup2CycleLen
      omega))]
  change t - (2 * n - 2) - 1 = t - (2 * n - 2) - 1
  rfl

lemma cup2Phase3Mover_nonstart_right_val (n : Nat) {t : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < 3 * n - 3) :
    (right (cup2Phase3Mover n t (by omega)
      (by
        unfold cup2CycleLen
        omega))).1 =
      t - (2 * n - 2) + 1 := by
  rw [right_val_of_not_top (i := cup2Phase3Mover n t (by omega)
    (by
      unfold cup2CycleLen
      omega))
    (cup2Phase3Mover_nonstart_not_top n ht0 ht)]
  change t - (2 * n - 2) + 1 = t - (2 * n - 2) + 1
  rfl

lemma cup2Cycle_phase3_nonstart_left_input (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < 3 * n - 3) :
    cup2CycleVal n t (left (cup2Phase3Mover n t (by omega)
      (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht))).1 = 0 := by
  have ht1 : ¬ t < n := by
    omega
  have ht2 : ¬ t < 2 * n - 2 := by
    omega
  have hboundary : t ≠ 2 * n - 2 := by
    omega
  rw [cup2Phase3Mover_nonstart_left_val n ht0 ht, cup2CycleVal_phase3 ht1 ht2 hboundary]
  have hk : t - (2 * n - 2) ≠ 0 := by
    omega
  have hlt : t - (2 * n - 2) - 1 < t - (2 * n - 2) := by
    omega
  simp [hk, hlt]

lemma cup2Cycle_phase3_nonstart_right_input (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < 3 * n - 3) :
    cup2CycleVal n t (right (cup2Phase3Mover n t (by omega)
      (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht))).1 =
      if t = 3 * n - 4 then 1 else 2 := by
  have ht1 : ¬ t < n := by
    omega
  have ht2 : ¬ t < 2 * n - 2 := by
    omega
  have hboundary : t ≠ 2 * n - 2 := by
    omega
  rw [cup2Phase3Mover_nonstart_right_val n ht0 ht, cup2CycleVal_phase3 ht1 ht2 hboundary]
  have hk : t - (2 * n - 2) ≠ 0 := by
    omega
  by_cases hhigh : t = 3 * n - 4
  · subst t
    have hcut : 3 * n - 4 - (2 * n - 2) = n - 2 := by
      omega
    have hge : ¬ (n - 2 + 1 < n - 2) := by
      omega
    have htop : ¬ (n - 2 + 1 < n - 1) := by
      omega
    simp [hcut, hge, htop]
  · have hnot : ¬ t - (2 * n - 2) + 1 < t - (2 * n - 2) := by
      omega
    have hlt : t - (2 * n - 2) + 1 < n - 1 := by
      omega
    simp [hk, hnot, hlt, hhigh]

lemma cup2Cycle_phase3_nonstart_output (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < 3 * n - 3) :
    cup2OutVal n (cup2Phase3Mover n t (by omega)
      (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)) 0 2
      (if t = 3 * n - 4 then 1 else 2) = 0 := by
  by_cases hlow : t = 2 * n - 1
  · subst t
    have hm : 2 * n - 1 - (2 * n - 2) = 1 := by
      omega
    have h0 : ¬ (1 : Nat) = 0 := by
      decide
    have hhigh : ¬ 1 + 2 = n := by
      omega
    have hlast : ¬ 2 * n - 1 = 3 * n - 4 := by
      omega
    simpa [cup2OutVal, cup2Phase3Mover, hm, h0, hhigh, hlast] using lookup_low_022
  · by_cases hhigh : t = 3 * n - 4
    · subst t
      have hm : 3 * n - 4 - (2 * n - 2) = n - 2 := by
        omega
      have h0 : ¬ n - 2 = 0 := by
        omega
      have h1 : ¬ n - 2 = 1 := by
        omega
      have htop : ¬ n - 2 + 1 = n := by
        omega
      have hhigh' : n - 2 + 2 = n := by
        omega
      simpa [cup2OutVal, cup2Phase3Mover, hm, h0, h1, htop, hhigh'] using lookup_high_021
    · have h0 : ¬ t - (2 * n - 2) = 0 := by
        omega
      have h1 : ¬ t - (2 * n - 2) = 1 := by
        omega
      have htop : ¬ (t - (2 * n - 2)) + 1 = n := by
        omega
      have hhigh' : ¬ (t - (2 * n - 2)) + 2 = n := by
        omega
      simpa [cup2OutVal, cup2Phase3Mover, h0, h1, htop, hhigh', hhigh] using lookup_mid_022

lemma cup2Cycle_phase3_nonstart_trans_val (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < 3 * n - 3) :
    ((cup2System n hn).f
      (cup2Phase3Mover n t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht))
      (cup2Phase3Config n hn t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)
        (left (cup2Phase3Mover n t (by omega)
          (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht))))
      (cup2Phase3Config n hn t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)
        (cup2Phase3Mover n t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)))
      (cup2Phase3Config n hn t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)
        (right (cup2Phase3Mover n t (by omega)
          (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht))))).1 = 0 := by
  let mover : Fin n :=
    cup2Phase3Mover n t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)
  let cfg : Config (cup2Spec n hn) :=
    cup2Phase3Config n hn t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)
  rw [show (cup2System n hn).f = cup2Trans n hn by rfl]
  rw [cup2Trans_val]
  change cup2OutVal n mover ((cfg (left mover)).1) ((cfg mover).1) ((cfg (right mover)).1) = 0
  have hleft : (cfg (left mover)).1 = 0 := by
    dsimp [cfg]
    change cup2CycleVal n t (left mover).1 = 0
    simpa [mover] using cup2Cycle_phase3_nonstart_left_input n hn ht0 ht
  have hself : (cfg mover).1 = 2 := by
    dsimp [cfg]
    change cup2CycleVal n t mover.1 = 2
    simpa [mover, cup2Phase3Mover] using cup2Cycle_phase3_nonstart_self n ht0 ht
  have hright : (cfg (right mover)).1 = if t = 3 * n - 4 then 1 else 2 := by
    dsimp [cfg]
    change cup2CycleVal n t (right mover).1 = if t = 3 * n - 4 then 1 else 2
    simpa [mover] using cup2Cycle_phase3_nonstart_right_input n hn ht0 ht
  rw [hleft, hself, hright]
  simpa [mover] using cup2Cycle_phase3_nonstart_output n hn ht0 ht

lemma cup2Cycle_phase3_nonstart_privileged (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < 3 * n - 3) :
    privileged (cup2System n hn)
      (cup2Phase3Config n hn t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht))
      (cup2Phase3Mover n t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)) := by
  rw [privileged]
  intro hEq
  have hval := congrArg Fin.val hEq
  have hout :
      ((cup2System n hn).f
        (cup2Phase3Mover n t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht))
        (cup2Phase3Config n hn t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)
          (left (cup2Phase3Mover n t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht))))
        (cup2Phase3Config n hn t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)
          (cup2Phase3Mover n t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)))
        (cup2Phase3Config n hn t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)
          (right (cup2Phase3Mover n t (by omega)
            (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht))))).1 = 0 :=
    cup2Cycle_phase3_nonstart_trans_val n hn ht0 ht
  have hself :
      (cup2Phase3Config n hn t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)
        (cup2Phase3Mover n t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht))).1 = 2 := by
    simpa [cup2Phase3Config, cup2Phase3Mover] using cup2Cycle_phase3_nonstart_self n ht0 ht
  rw [hout, hself] at hval
  omega

lemma cup2Cycle_phase3_nonstart_nonmover_trans_val (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < 3 * n - 3) (i : Fin n)
    (hi : i ≠ cup2Phase3Mover n t (by omega)
      (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)) :
    ((cup2System n hn).f i
      (cup2Phase3Config n hn t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)
        (left i))
      (cup2Phase3Config n hn t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)
        i)
      (cup2Phase3Config n hn t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)
        (right i))).1 =
      (cup2Phase3Config n hn t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)
        i).1 := by
  let cfg : Config (cup2Spec n hn) :=
    cup2Phase3Config n hn t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)
  rw [show (cup2System n hn).f = cup2Trans n hn by rfl]
  rw [cup2Trans_val]
  change cup2OutVal n i ((cfg (left i)).1) ((cfg i).1) ((cfg (right i)).1) = (cfg i).1
  have hmover : i.1 ≠ t - (2 * n - 2) := by
    intro hm
    apply hi
    ext
    simpa [cup2Phase3Mover] using hm
  by_cases h0 : i.1 = 0
  · have hleft : (cfg (left i)).1 = 1 := by
      dsimp [cfg]
      change cup2CycleVal n t (left i).1 = 1
      have hleft_idx : (left i).1 = n - 1 := by
        rw [left_val, h0, Nat.zero_add]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hleft_idx]
      simpa using cup2Cycle_phase3_nonstart_top_val n ht0 ht
    have hself : (cfg i).1 = 0 := by
      dsimp [cfg]
      change cup2CycleVal n t i.1 = 0
      rw [h0]
      exact cup2Cycle_phase3_nonstart_zero_before_mover n ht0 ht (by omega)
    have hright_idx : (right i).1 = 1 := by
      have htop : i.1 + 1 ≠ n := by
        omega
      rw [right_val_of_not_top (i := i) htop, h0]
    by_cases hstart : t = 2 * n - 1
    · have hright : (cfg (right i)).1 = 2 := by
        dsimp [cfg]
        change cup2CycleVal n t (right i).1 = 2
        rw [hright_idx]
        exact cup2Cycle_phase3_nonstart_two_before_top n ht0 ht (by omega) (by omega)
      rw [hleft, hself, hright]
      simpa [cup2OutVal, h0, hstart] using lookup_bot_102
    · have hright : (cfg (right i)).1 = 0 := by
        dsimp [cfg]
        change cup2CycleVal n t (right i).1 = 0
        rw [hright_idx]
        exact cup2Cycle_phase3_nonstart_zero_before_mover n ht0 ht (by omega)
      rw [hleft, hself, hright]
      simpa [cup2OutVal, h0, hstart] using lookup_bot_100
  · by_cases h1 : i.1 = 1
    · have hleft : (cfg (left i)).1 = 0 := by
        dsimp [cfg]
        change cup2CycleVal n t (left i).1 = 0
        have hleft_idx : (left i).1 = 0 := by
          rw [left_val_of_ne_zero (i := i) h0, h1]
        rw [hleft_idx]
        exact cup2Cycle_phase3_nonstart_zero_before_mover n ht0 ht (by omega)
      have hself : (cfg i).1 = 0 := by
        dsimp [cfg]
        change cup2CycleVal n t i.1 = 0
        rw [h1]
        exact cup2Cycle_phase3_nonstart_zero_before_mover n ht0 ht (by omega)
      have hright_idx : (right i).1 = 2 := by
        have htop : i.1 + 1 ≠ n := by
          omega
        rw [right_val_of_not_top (i := i) htop, h1]
      by_cases hnext : t = 2 * n
      · have hright : (cfg (right i)).1 = 2 := by
          dsimp [cfg]
          change cup2CycleVal n t (right i).1 = 2
          rw [hright_idx]
          exact cup2Cycle_phase3_nonstart_two_before_top n ht0 ht (by omega) (by omega)
        rw [hleft, hself, hright]
        simpa [cup2OutVal, h0, h1, hnext] using lookup_low_002
      · have hright : (cfg (right i)).1 = 0 := by
          dsimp [cfg]
          change cup2CycleVal n t (right i).1 = 0
          rw [hright_idx]
          exact cup2Cycle_phase3_nonstart_zero_before_mover n ht0 ht (by omega)
        rw [hleft, hself, hright]
        simpa [cup2OutVal, h0, h1, hnext] using lookup_low_000
    · by_cases htop : i.1 + 1 = n
      · have hleft : (cfg (left i)).1 = 2 := by
          dsimp [cfg]
          change cup2CycleVal n t (left i).1 = 2
          have hleft_idx : (left i).1 = n - 2 := by
            rw [left_val_of_ne_zero (i := i) h0]
            omega
          rw [hleft_idx]
          exact cup2Cycle_phase3_nonstart_two_before_top n ht0 ht (by omega) (by omega)
        have hself : (cfg i).1 = 1 := by
          dsimp [cfg]
          change cup2CycleVal n t i.1 = 1
          rw [show i.1 = n - 1 by omega]
          simpa using cup2Cycle_phase3_nonstart_top_val n ht0 ht
        have hright : (cfg (right i)).1 = 0 := by
          dsimp [cfg]
          change cup2CycleVal n t (right i).1 = 0
          rw [right_val_of_top (i := i) htop]
          exact cup2Cycle_phase3_nonstart_zero_before_mover n ht0 ht (by omega)
        rw [hleft, hself, hright]
        simpa [cup2OutVal, h0, h1, htop] using lookup_top_210
      · by_cases hhigh : i.1 + 2 = n
        · have hleft : (cfg (left i)).1 = 2 := by
            dsimp [cfg]
            change cup2CycleVal n t (left i).1 = 2
            have hleft_idx : (left i).1 = n - 3 := by
              rw [left_val_of_ne_zero (i := i) h0]
              omega
            rw [hleft_idx]
            exact cup2Cycle_phase3_nonstart_two_before_top n ht0 ht (by omega) (by omega)
          have hself : (cfg i).1 = 2 := by
            dsimp [cfg]
            change cup2CycleVal n t i.1 = 2
            exact cup2Cycle_phase3_nonstart_two_before_top n ht0 ht (by omega) (by omega)
          have hright : (cfg (right i)).1 = 1 := by
            dsimp [cfg]
            change cup2CycleVal n t (right i).1 = 1
            have hright_idx : (right i).1 = n - 1 := by
              rw [right_val_of_not_top (i := i) htop]
              omega
            rw [hright_idx]
            simpa using cup2Cycle_phase3_nonstart_top_val n ht0 ht
          rw [hleft, hself, hright]
          simpa [cup2OutVal, h0, h1, htop, hhigh] using lookup_high_221
        · by_cases hadj : i.1 + 1 = t - (2 * n - 2)
          · have hleft : (cfg (left i)).1 = 0 := by
              dsimp [cfg]
              change cup2CycleVal n t (left i).1 = 0
              have hleft_idx : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
              rw [hleft_idx]
              exact cup2Cycle_phase3_nonstart_zero_before_mover n ht0 ht (by omega)
            have hself : (cfg i).1 = 0 := by
              dsimp [cfg]
              change cup2CycleVal n t i.1 = 0
              exact cup2Cycle_phase3_nonstart_zero_before_mover n ht0 ht (by omega)
            have hright : (cfg (right i)).1 = 2 := by
              dsimp [cfg]
              change cup2CycleVal n t (right i).1 = 2
              have hright_idx : (right i).1 = i.1 + 1 := right_val_of_not_top htop
              rw [hright_idx]
              exact cup2Cycle_phase3_nonstart_two_before_top n ht0 ht (by omega) (by omega)
            rw [hleft, hself, hright]
            simpa [cup2OutVal, h0, h1, htop, hhigh] using lookup_mid_002
          · by_cases hlt : i.1 < t - (2 * n - 2)
            · have hleft : (cfg (left i)).1 = 0 := by
                dsimp [cfg]
                change cup2CycleVal n t (left i).1 = 0
                have hleft_idx : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
                rw [hleft_idx]
                exact cup2Cycle_phase3_nonstart_zero_before_mover n ht0 ht (by omega)
              have hself : (cfg i).1 = 0 := by
                dsimp [cfg]
                change cup2CycleVal n t i.1 = 0
                exact cup2Cycle_phase3_nonstart_zero_before_mover n ht0 ht hlt
              have hright : (cfg (right i)).1 = 0 := by
                dsimp [cfg]
                change cup2CycleVal n t (right i).1 = 0
                have hright_idx : (right i).1 = i.1 + 1 := right_val_of_not_top htop
                rw [hright_idx]
                exact cup2Cycle_phase3_nonstart_zero_before_mover n ht0 ht (by omega)
              rw [hleft, hself, hright]
              simpa [cup2OutVal, h0, h1, htop, hhigh] using lookup_mid_000
            · have hleft : (cfg (left i)).1 = 2 := by
                dsimp [cfg]
                change cup2CycleVal n t (left i).1 = 2
                have hleft_idx : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
                rw [hleft_idx]
                exact cup2Cycle_phase3_nonstart_two_before_top n ht0 ht (by omega) (by omega)
              have hself : (cfg i).1 = 2 := by
                dsimp [cfg]
                change cup2CycleVal n t i.1 = 2
                exact cup2Cycle_phase3_nonstart_two_before_top n ht0 ht (by omega) (by omega)
              have hright : (cfg (right i)).1 = 2 := by
                dsimp [cfg]
                change cup2CycleVal n t (right i).1 = 2
                have hright_idx : (right i).1 = i.1 + 1 := right_val_of_not_top htop
                rw [hright_idx]
                exact cup2Cycle_phase3_nonstart_two_before_top n ht0 ht (by omega) (by omega)
              rw [hleft, hself, hright]
              simpa [cup2OutVal, h0, h1, htop, hhigh] using lookup_mid_222

lemma cup2Cycle_phase3_nonstart_nonmover_not_privileged (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < 3 * n - 3) (i : Fin n)
    (hi : i ≠ cup2Phase3Mover n t (by omega)
      (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)) :
    ¬ privileged (cup2System n hn)
      (cup2Phase3Config n hn t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht))
      i := by
  rw [privileged]
  intro hneq
  apply hneq
  apply Fin.ext
  exact cup2Cycle_phase3_nonstart_nonmover_trans_val n hn ht0 ht i hi

lemma cup2Cycle_phase3_nonstart_singlePrivileged (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < 3 * n - 3) :
    ∃! i, privileged (cup2System n hn)
      (cup2Phase3Config n hn t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht))
      i := by
  refine ⟨cup2Phase3Mover n t (by omega)
      (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht),
    cup2Cycle_phase3_nonstart_privileged n hn ht0 ht, ?_⟩
  intro i hi
  by_contra hne
  exact (cup2Cycle_phase3_nonstart_nonmover_not_privileged n hn ht0 ht i hne) hi

lemma cup2Cycle_phase3_nonstart_stable (n : Nat) (hn : 4 ≤ n) {t j : Nat}
    (ht0 : 2 * n - 1 ≤ t) (_ht : t < 3 * n - 3) (_hj : j < n)
    (hjt : j ≠ t - (2 * n - 2)) :
    cup2CycleVal n (t + 1) j = cup2CycleVal n t j := by
  have ht1 : ¬ t < n := by
    omega
  have ht2 : ¬ t < 2 * n - 2 := by
    omega
  have hboundary : t ≠ 2 * n - 2 := by
    omega
  have ht1' : ¬ t + 1 < n := by
    omega
  have ht2' : ¬ t + 1 < 2 * n - 2 := by
    omega
  have hboundary' : t + 1 ≠ 2 * n - 2 := by
    omega
  rw [cup2CycleVal_phase3 ht1 ht2 hboundary, cup2CycleVal_phase3 ht1' ht2' hboundary']
  have hk : t - (2 * n - 2) ≠ 0 := by
    omega
  have hk' : t + 1 - (2 * n - 2) ≠ 0 := by
    omega
  simp [hk, hk']
  by_cases hjk : j < t - (2 * n - 2)
  · have hjk' : j < t + 1 - (2 * n - 2) := by
      omega
    simp [hjk, hjk']
  · have hjk' : ¬ j < t + 1 - (2 * n - 2) := by
      omega
    simp [hjk, hjk']

lemma cup2Cycle_phase3_nonstart_step (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (ht0 : 2 * n - 1 ≤ t) (ht : t < 3 * n - 3) :
    move (cup2System n hn)
      (cup2Phase3Config n hn t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht))
      (cup2Phase3Mover n t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)) =
      cup2CycleConfig n hn ⟨t + 1, lt_cup2CycleLen_of_phase3_succ n hn (by omega) ht⟩ := by
  funext i
  by_cases hi : i = cup2Phase3Mover n t (by omega) (lt_cup2CycleLen_of_phase3_interior n hn (by omega) ht)
  · subst hi
    apply Fin.ext
    simp [move]
    rw [cup2Cycle_phase3_nonstart_trans_val n hn ht0 ht]
    symm
    simpa [cup2Phase3Mover] using cup2Cycle_phase3_nonstart_next n hn ht0 ht
  · apply Fin.ext
    simp [move, hi, cup2Phase3Config, cup2CycleConfig]
    symm
    exact cup2Cycle_phase3_nonstart_stable n hn ht0 ht i.2 (by
      intro h
      apply hi
      ext
      simpa [cup2Phase3Mover] using h)

lemma cup2Cycle_zero_val (n : Nat) (hn : 4 ≤ n) {j : Nat} (_hj : j < n) :
    cup2CycleVal n 0 j = 0 := by
  have h0 : 0 < n := by
    omega
  rw [cup2CycleVal_phase1 h0]
  simp

lemma cup2Cycle_phase3_last_val (n : Nat) (hn : 4 ≤ n) {j : Nat} (_hj : j < n) :
    cup2CycleVal n (3 * n - 3) j = if j < n - 1 then 0 else 1 := by
  have ht1 : ¬ 3 * n - 3 < n := by
    omega
  have ht2 : ¬ 3 * n - 3 < 2 * n - 2 := by
    omega
  have hboundary : 3 * n - 3 ≠ 2 * n - 2 := by
    omega
  rw [cup2CycleVal_phase3 ht1 ht2 hboundary]
  have hcut : 3 * n - 3 - (2 * n - 2) = n - 1 := by
    omega
  have hne : n - 1 ≠ 0 := by
    omega
  rw [hcut]
  by_cases hjlt : j < n - 1
  · simp [hne, hjlt]
  · simp [hne, hjlt]

lemma cup2Cycle_phase3_last_zero_before_top (n : Nat) (hn : 4 ≤ n) {j : Nat}
    (hj : j < n - 1) :
    cup2CycleVal n (3 * n - 3) j = 0 := by
  have hjn : j < n := by
    omega
  rw [cup2Cycle_phase3_last_val n hn hjn]
  simp [hj]

lemma cup2Cycle_phase3_last_left_input (n : Nat) (hn : 4 ≤ n) :
    cup2CycleVal n (3 * n - 3) (n - 2) = 0 := by
  have hj : n - 2 < n := by
    omega
  rw [cup2Cycle_phase3_last_val n hn hj]
  have hjlt : n - 2 < n - 1 := by
    omega
  simp [hjlt]

lemma cup2Cycle_phase3_last_self (n : Nat) (hn : 4 ≤ n) :
    cup2CycleVal n (3 * n - 3) (n - 1) = 1 := by
  have hj : n - 1 < n := by
    omega
  rw [cup2Cycle_phase3_last_val n hn hj]
  simp

lemma cup2Cycle_phase3_last_right_input (n : Nat) (hn : 4 ≤ n) :
    cup2CycleVal n (3 * n - 3) 0 = 0 := by
  have hj : 0 < n := by
    omega
  rw [cup2Cycle_phase3_last_val n hn hj]
  have hjlt : 0 < n - 1 := by
    omega
  simp [hjlt]

lemma cup2Cycle_phase3_last_output (n : Nat) (hn : 4 ≤ n) :
    cup2OutVal n (cup2Phase3LastMover n hn) 0 1 0 = 0 := by
  have h0 : ¬ 3 * n - 3 - (2 * n - 2) = 0 := by
    omega
  have h1 : ¬ 3 * n - 3 - (2 * n - 2) = 1 := by
    omega
  have htop : 3 * n - 3 - (2 * n - 2) + 1 = n := by
    omega
  simpa [cup2OutVal, cup2Phase3LastMover, cup2Phase3Mover, h0, h1, htop] using lookup_top_010

lemma cup2Cycle_phase3_last_trans_val (n : Nat) (hn : 4 ≤ n) :
    ((cup2System n hn).f (cup2Phase3LastMover n hn)
      (cup2Phase3LastConfig n hn (left (cup2Phase3LastMover n hn)))
      (cup2Phase3LastConfig n hn (cup2Phase3LastMover n hn))
      (cup2Phase3LastConfig n hn (right (cup2Phase3LastMover n hn)))).1 = 0 := by
  let mover : Fin n := cup2Phase3LastMover n hn
  let cfg : Config (cup2Spec n hn) := cup2Phase3LastConfig n hn
  rw [show (cup2System n hn).f = cup2Trans n hn by rfl]
  rw [cup2Trans_val]
  change cup2OutVal n mover ((cfg (left mover)).1) ((cfg mover).1) ((cfg (right mover)).1) = 0
  have hleft : (cfg (left mover)).1 = 0 := by
    dsimp [cfg]
    change cup2CycleVal n (3 * n - 3) (left mover).1 = 0
    have hne : mover.1 ≠ 0 := by
      dsimp [mover]
      rw [cup2Phase3LastMover_val]
      omega
    rw [left_val_of_ne_zero (i := mover) hne]
    simpa [mover] using cup2Cycle_phase3_last_left_input n hn
  have hself : (cfg mover).1 = 1 := by
    dsimp [cfg]
    change cup2CycleVal n (3 * n - 3) mover.1 = 1
    simpa [mover] using cup2Cycle_phase3_last_self n hn
  have hright : (cfg (right mover)).1 = 0 := by
    dsimp [cfg]
    change cup2CycleVal n (3 * n - 3) (right mover).1 = 0
    have htop : mover.1 + 1 = n := by
      dsimp [mover]
      rw [cup2Phase3LastMover_val]
      omega
    rw [right_val_of_top (i := mover) htop]
    simpa using cup2Cycle_phase3_last_right_input n hn
  rw [hleft, hself, hright]
  simpa [mover] using cup2Cycle_phase3_last_output n hn

lemma cup2Cycle_phase3_last_privileged (n : Nat) (hn : 4 ≤ n) :
    privileged (cup2System n hn) (cup2Phase3LastConfig n hn) (cup2Phase3LastMover n hn) := by
  rw [privileged]
  intro hEq
  have hval := congrArg Fin.val hEq
  have hout :
      ((cup2System n hn).f (cup2Phase3LastMover n hn)
        (cup2Phase3LastConfig n hn (left (cup2Phase3LastMover n hn)))
        (cup2Phase3LastConfig n hn (cup2Phase3LastMover n hn))
        (cup2Phase3LastConfig n hn (right (cup2Phase3LastMover n hn)))).1 = 0 :=
    cup2Cycle_phase3_last_trans_val n hn
  have hself :
      (cup2Phase3LastConfig n hn (cup2Phase3LastMover n hn)).1 = 1 := by
    have hcut : 3 * n - 3 - (2 * n - 2) = n - 1 := by
      omega
    simpa [cup2Phase3LastConfig, cup2Phase3Config, cup2Phase3LastMover, cup2Phase3Mover, hcut] using
      cup2Cycle_phase3_last_self n hn
  rw [hout, hself] at hval
  omega

lemma cup2Cycle_phase3_last_nonmover_trans_val (n : Nat) (hn : 4 ≤ n) (i : Fin n)
    (hi : i ≠ cup2Phase3LastMover n hn) :
    ((cup2System n hn).f i
      (cup2Phase3LastConfig n hn (left i))
      (cup2Phase3LastConfig n hn i)
      (cup2Phase3LastConfig n hn (right i))).1 =
      (cup2Phase3LastConfig n hn i).1 := by
  rw [show (cup2System n hn).f = cup2Trans n hn by rfl]
  rw [cup2Trans_val]
  have htop : i.1 + 1 ≠ n := by
    intro hi_top
    apply hi
    ext
    rw [cup2Phase3LastMover_val n hn]
    omega
  by_cases h0 : i.1 = 0
  · have hleft : (cup2Phase3LastConfig n hn (left i)).1 = 1 := by
      change cup2CycleVal n (3 * n - 3) (left i).1 = 1
      have hleft_idx : (left i).1 = n - 1 := by
        rw [left_val, h0]
        have hlt : n - 1 < n := by
          omega
        rw [Nat.zero_add]
        exact Nat.mod_eq_of_lt hlt
      rw [hleft_idx]
      simpa using cup2Cycle_phase3_last_self n hn
    have hself : (cup2Phase3LastConfig n hn i).1 = 0 := by
      change cup2CycleVal n (3 * n - 3) i.1 = 0
      rw [h0]
      simpa using cup2Cycle_phase3_last_zero_before_top n hn (j := 0) (by omega)
    have hright : (cup2Phase3LastConfig n hn (right i)).1 = 0 := by
      change cup2CycleVal n (3 * n - 3) (right i).1 = 0
      have hright_idx : (right i).1 = 1 := by
        rw [right_val_of_not_top (i := i) htop, h0]
      rw [hright_idx]
      simpa using cup2Cycle_phase3_last_zero_before_top n hn (j := 1) (by omega)
    rw [hleft, hself, hright]
    simpa [cup2OutVal, h0] using lookup_bot_100
  · by_cases h1 : i.1 = 1
    · have hleft : (cup2Phase3LastConfig n hn (left i)).1 = 0 := by
        change cup2CycleVal n (3 * n - 3) (left i).1 = 0
        have hleft_idx : (left i).1 = 0 := by
          rw [left_val_of_ne_zero (i := i) h0, h1]
        rw [hleft_idx]
        simpa using cup2Cycle_phase3_last_zero_before_top n hn (j := 0) (by omega)
      have hself : (cup2Phase3LastConfig n hn i).1 = 0 := by
        change cup2CycleVal n (3 * n - 3) i.1 = 0
        rw [h1]
        simpa using cup2Cycle_phase3_last_zero_before_top n hn (j := 1) (by omega)
      have hright : (cup2Phase3LastConfig n hn (right i)).1 = 0 := by
        change cup2CycleVal n (3 * n - 3) (right i).1 = 0
        have hright_idx : (right i).1 = 2 := by
          rw [right_val_of_not_top (i := i) htop, h1]
        rw [hright_idx]
        simpa using cup2Cycle_phase3_last_zero_before_top n hn (j := 2) (by omega)
      rw [hleft, hself, hright]
      simpa [cup2OutVal, h0, h1] using lookup_low_000
    · by_cases hhigh : i.1 + 2 = n
      · have hleft : (cup2Phase3LastConfig n hn (left i)).1 = 0 := by
          change cup2CycleVal n (3 * n - 3) (left i).1 = 0
          have hleft_idx : (left i).1 = n - 3 := by
            rw [left_val_of_ne_zero (i := i) h0]
            omega
          rw [hleft_idx]
          simpa using cup2Cycle_phase3_last_zero_before_top n hn (j := n - 3) (by omega)
        have hself : (cup2Phase3LastConfig n hn i).1 = 0 := by
          change cup2CycleVal n (3 * n - 3) i.1 = 0
          have hi_lt : i.1 < n - 1 := by
            omega
          simpa using cup2Cycle_phase3_last_zero_before_top n hn (j := i.1) hi_lt
        have hright : (cup2Phase3LastConfig n hn (right i)).1 = 1 := by
          change cup2CycleVal n (3 * n - 3) (right i).1 = 1
          have hright_idx : (right i).1 = n - 1 := by
            rw [right_val_of_not_top (i := i) htop]
            omega
          rw [hright_idx]
          simpa using cup2Cycle_phase3_last_self n hn
        rw [hleft, hself, hright]
        simpa [cup2OutVal, h0, h1, htop, hhigh] using lookup_high_001
      · have hleft : (cup2Phase3LastConfig n hn (left i)).1 = 0 := by
          change cup2CycleVal n (3 * n - 3) (left i).1 = 0
          have hleft_idx : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
          rw [hleft_idx]
          have hlt : i.1 - 1 < n - 1 := by
            omega
          simpa using cup2Cycle_phase3_last_zero_before_top n hn (j := i.1 - 1) hlt
        have hself : (cup2Phase3LastConfig n hn i).1 = 0 := by
          change cup2CycleVal n (3 * n - 3) i.1 = 0
          have hi_lt : i.1 < n - 1 := by
            omega
          simpa using cup2Cycle_phase3_last_zero_before_top n hn (j := i.1) hi_lt
        have hright : (cup2Phase3LastConfig n hn (right i)).1 = 0 := by
          change cup2CycleVal n (3 * n - 3) (right i).1 = 0
          have hright_idx : (right i).1 = i.1 + 1 := right_val_of_not_top htop
          rw [hright_idx]
          have hlt : i.1 + 1 < n - 1 := by
            omega
          simpa using cup2Cycle_phase3_last_zero_before_top n hn (j := i.1 + 1) hlt
        rw [hleft, hself, hright]
        simpa [cup2OutVal, h0, h1, htop, hhigh] using lookup_mid_000

lemma cup2Cycle_phase3_last_nonmover_not_privileged (n : Nat) (hn : 4 ≤ n) (i : Fin n)
    (hi : i ≠ cup2Phase3LastMover n hn) :
    ¬ privileged (cup2System n hn) (cup2Phase3LastConfig n hn) i := by
  rw [privileged]
  intro hneq
  apply hneq
  apply Fin.ext
  exact cup2Cycle_phase3_last_nonmover_trans_val n hn i hi

lemma cup2Cycle_phase3_last_singlePrivileged (n : Nat) (hn : 4 ≤ n) :
    ∃! i, privileged (cup2System n hn) (cup2Phase3LastConfig n hn) i := by
  refine ⟨cup2Phase3LastMover n hn, cup2Cycle_phase3_last_privileged n hn, ?_⟩
  intro i hi
  by_contra hne
  exact (cup2Cycle_phase3_last_nonmover_not_privileged n hn i hne) hi

lemma cup2Cycle_phase3_last_stable (n : Nat) (hn : 4 ≤ n) {j : Nat} (hj : j < n)
    (hjt : j ≠ n - 1) :
    cup2CycleVal n 0 j = cup2CycleVal n (3 * n - 3) j := by
  rw [cup2Cycle_zero_val n hn hj, cup2Cycle_phase3_last_val n hn hj]
  have hjlt : j < n - 1 := by
    omega
  simp [hjlt]

lemma cup2Cycle_phase3_last_step (n : Nat) (hn : 4 ≤ n) :
    move (cup2System n hn) (cup2Phase3LastConfig n hn) (cup2Phase3LastMover n hn) =
      cup2CycleConfig n hn ⟨0, by
        unfold cup2CycleLen
        omega⟩ := by
  funext i
  by_cases hi : i = cup2Phase3LastMover n hn
  · subst hi
    apply Fin.ext
    simp [move]
    rw [cup2Cycle_phase3_last_trans_val]
    symm
    simpa [cup2Phase3LastMover_val n hn] using
      cup2Cycle_zero_val n hn (j := n - 1) (by omega)
  · apply Fin.ext
    simp [move, hi, cup2Phase3LastConfig, cup2Phase3Config]
    symm
    exact cup2Cycle_phase3_last_stable n hn i.2 (by
      intro h
      apply hi
      ext
      simpa [cup2Phase3LastMover_val n hn] using h)

lemma cup2CycleConfigs_get_eq (n : Nat) (hn : 4 ≤ n)
    (k : Fin (cup2CycleConfigs n hn).length) :
    (cup2CycleConfigs n hn).get k =
      cup2CycleConfig n hn ⟨k.1, by
        simpa [cup2CycleConfigs] using k.2⟩ := by
  simpa [cup2CycleConfigs] using (List.get_ofFn (f := cup2CycleConfig n hn) k)

lemma cup2CycleConfigs_get_next_eq (n : Nat) (hn : 4 ≤ n)
    (k : Fin (cup2CycleConfigs n hn).length) :
    (cup2CycleConfigs n hn).get (nextIndex (cup2CycleConfigs n hn) k) =
      cup2CycleConfig n hn
        (cup2CycleNext n ⟨k.1, by
          simpa [cup2CycleConfigs] using k.2⟩) := by
  let t : Fin (cup2CycleLen n) := ⟨k.1, by
    simpa [cup2CycleConfigs] using k.2⟩
  have hcast :
      Fin.cast (by simp [cup2CycleConfigs]) (nextIndex (cup2CycleConfigs n hn) k) =
        cup2CycleNext n t := by
    ext
    simp [nextIndex, cup2CycleNext, t, cup2CycleConfigs]
  simpa [cup2CycleConfigs, t] using congrArg (cup2CycleConfig n hn) hcast

lemma cup2CycleNext_phase1 (n : Nat) (hn : 4 ≤ n) {t : Fin (cup2CycleLen n)}
    (ht : t.1 < n) :
    cup2CycleNext n t = ⟨t.1 + 1, lt_cup2CycleLen_of_phase1_succ n hn ht⟩ := by
  ext
  simp [cup2CycleNext, Nat.mod_eq_of_lt (lt_cup2CycleLen_of_phase1_succ n hn ht)]

lemma cup2CycleNext_phase2 (n : Nat) (hn : 4 ≤ n) {t : Fin (cup2CycleLen n)}
    (htn : n ≤ t.1) (ht : t.1 < 2 * n - 2) :
    cup2CycleNext n t = ⟨t.1 + 1, lt_cup2CycleLen_of_phase2_succ n hn htn ht⟩ := by
  ext
  simp [cup2CycleNext, Nat.mod_eq_of_lt (lt_cup2CycleLen_of_phase2_succ n hn htn ht)]

lemma cup2CycleNext_phase3_interior (n : Nat) (hn : 4 ≤ n) {t : Fin (cup2CycleLen n)}
    (ht0 : 2 * n - 2 ≤ t.1) (ht : t.1 < 3 * n - 3) :
    cup2CycleNext n t = ⟨t.1 + 1, lt_cup2CycleLen_of_phase3_succ n hn ht0 ht⟩ := by
  ext
  simp [cup2CycleNext, Nat.mod_eq_of_lt (lt_cup2CycleLen_of_phase3_succ n hn ht0 ht)]

lemma cup2CycleNext_phase3_start (n : Nat) (hn : 4 ≤ n) :
    cup2CycleNext n ⟨2 * n - 2,
        lt_cup2CycleLen_of_phase3_interior n hn (by omega) (by omega)⟩ =
      ⟨2 * n - 1, phase3StartNext_lt n hn⟩ := by
  ext
  change (2 * n - 2 + 1) % cup2CycleLen n = 2 * n - 1
  have hlt : 2 * n - 1 < cup2CycleLen n := phase3StartNext_lt n hn
  have hsum : 2 * n - 2 + 1 = 2 * n - 1 := by
    omega
  rw [hsum, Nat.mod_eq_of_lt hlt]

lemma cup2CycleNext_phase3_last (n : Nat) (hn : 4 ≤ n) :
    cup2CycleNext n ⟨3 * n - 3, phase3_last_lt n hn⟩ =
      ⟨0, by
        unfold cup2CycleLen
        omega⟩ := by
  ext
  change (3 * n - 3 + 1) % cup2CycleLen n = 0
  have hlen : 3 * n - 3 + 1 = cup2CycleLen n := by
    unfold cup2CycleLen
    omega
  rw [hlen, Nat.mod_self]

theorem cup2Cycle_closed_step (n : Nat) (hn : 4 ≤ n)
    (k : Fin (cup2CycleConfigs n hn).length) :
    ∃ i,
      privileged (cup2System n hn) ((cup2CycleConfigs n hn).get k) i ∧
        (cup2CycleConfigs n hn).get (nextIndex (cup2CycleConfigs n hn) k) =
          move (cup2System n hn) ((cup2CycleConfigs n hn).get k) i := by
  let t : Fin (cup2CycleLen n) := ⟨k.1, by
    simpa [cup2CycleConfigs] using k.2⟩
  have hk :
      (cup2CycleConfigs n hn).get k = cup2CycleConfig n hn t := by
    simpa [t] using cup2CycleConfigs_get_eq n hn k
  have hkNext :
      (cup2CycleConfigs n hn).get (nextIndex (cup2CycleConfigs n hn) k) =
        cup2CycleConfig n hn (cup2CycleNext n t) := by
    simpa [t] using cup2CycleConfigs_get_next_eq n hn k
  by_cases ht1 : t.1 < n
  · refine ⟨cup2Phase1Mover n t.1 ht1, ?_, ?_⟩
    · rw [hk]
      simpa [t, cup2Phase1Config] using cup2Cycle_phase1_privileged n hn ht1
    · rw [hk, hkNext, cup2CycleNext_phase1 n hn ht1]
      simpa [t, cup2Phase1Config] using (cup2Cycle_phase1_step n hn ht1).symm
  · by_cases ht2 : t.1 < 2 * n - 2
    · have htn : n ≤ t.1 := by
        omega
      refine ⟨cup2Phase2Mover n t.1 htn ht2, ?_, ?_⟩
      · rw [hk]
        simpa [t, cup2Phase2Config] using cup2Cycle_phase2_privileged n hn htn ht2
      · rw [hk, hkNext, cup2CycleNext_phase2 n hn htn ht2]
        simpa [t, cup2Phase2Config] using (cup2Cycle_phase2_step n hn htn ht2).symm
    · by_cases hstart : t.1 = 2 * n - 2
      · refine ⟨cup2Phase3StartMover n hn, ?_, ?_⟩
        · have htEq :
              t = ⟨2 * n - 2,
                lt_cup2CycleLen_of_phase3_interior n hn (by omega) (by omega)⟩ := by
            ext
            simpa [t] using hstart
          rw [hk, htEq]
          simpa [cup2Phase3StartConfig, cup2Phase3Config] using
              cup2Cycle_phase3_start_privileged n hn
        · have ht0 : 2 * n - 2 ≤ t.1 := by
            omega
          have ht : t.1 < 3 * n - 3 := by
            omega
          have htEq :
              t = ⟨2 * n - 2,
                lt_cup2CycleLen_of_phase3_interior n hn (by omega) (by omega)⟩ := by
            ext
            simpa [t] using hstart
          rw [hk, hkNext, htEq, cup2CycleNext_phase3_start n hn]
          simpa [cup2Phase3StartConfig, cup2Phase3Config] using
            (cup2Cycle_phase3_start_step n hn).symm
      · by_cases hphase3 : t.1 < 3 * n - 3
        · have ht0 : 2 * n - 1 ≤ t.1 := by
            omega
          refine ⟨cup2Phase3Mover n t.1 (by omega)
              (lt_cup2CycleLen_of_phase3_interior n hn (by omega) hphase3), ?_, ?_⟩
          · rw [hk]
            simpa [t, cup2Phase3Config] using
                cup2Cycle_phase3_nonstart_privileged n hn ht0 hphase3
          · rw [hk, hkNext, cup2CycleNext_phase3_interior n hn (by omega) hphase3]
            simpa [t, cup2Phase3Config] using
              (cup2Cycle_phase3_nonstart_step n hn ht0 hphase3).symm
        · have hlast : t.1 = 3 * n - 3 := by
            have hlt : t.1 < cup2CycleLen n := t.2
            unfold cup2CycleLen at hlt
            omega
          have htEq : t = ⟨3 * n - 3, phase3_last_lt n hn⟩ := by
            ext
            simpa [t] using hlast
          refine ⟨cup2Phase3LastMover n hn, ?_, ?_⟩
          · rw [hk, htEq]
            simpa [cup2Phase3LastConfig, cup2Phase3Config] using
                cup2Cycle_phase3_last_privileged n hn
          · rw [hk, hkNext, htEq, cup2CycleNext_phase3_last n hn]
            simpa [cup2Phase3LastConfig, cup2Phase3Config] using
              (cup2Cycle_phase3_last_step n hn).symm

lemma cup2CycleConfig_eq_val (n : Nat) (hn : 4 ≤ n) {t₁ t₂ : Fin (cup2CycleLen n)}
    (heq : cup2CycleConfig n hn t₁ = cup2CycleConfig n hn t₂) (j : Fin n) :
    cup2CycleVal n t₁.1 j.1 = cup2CycleVal n t₂.1 j.1 := by
  simpa using congrArg Fin.val (congrFun heq j)

lemma cup2Cycle_phase1_top_val (n : Nat) {t : Nat} (ht : t < n) :
    cup2CycleVal n t (n - 1) = 0 := by
  exact cup2Cycle_phase1_zero_from_mover n ht (j := n - 1) (by omega)

lemma cup2Cycle_nonphase1_top_val (n : Nat) (hn : 4 ≤ n) {t : Nat}
    (ht1 : ¬ t < n) (htCycle : t < cup2CycleLen n) :
    cup2CycleVal n t (n - 1) = 1 := by
  by_cases ht2 : t < 2 * n - 2
  · have htn : n ≤ t := by omega
    exact cup2Cycle_phase2_top_val n htn ht2
  · by_cases hstart : t = 2 * n - 2
    · rw [hstart]
      simpa using cup2Cycle_phase3_start_left_input n hn
    · by_cases hphase3 : t < 3 * n - 3
      · have ht0 : 2 * n - 1 ≤ t := by omega
        exact cup2Cycle_phase3_nonstart_top_val n ht0 hphase3
      · have hlast : t = 3 * n - 3 := by
          unfold cup2CycleLen at htCycle
          omega
        rw [hlast]
        simpa using cup2Cycle_phase3_last_self n hn

lemma cup2CycleConfig_injective (n : Nat) (hn : 4 ≤ n) :
    Function.Injective (cup2CycleConfig n hn) := by
  intro t₁ t₂ heq
  by_cases ht₁_phase1 : t₁.1 < n
  · by_cases ht₂_phase1 : t₂.1 < n
    · by_cases hlt : t₁.1 < t₂.1
      · let j : Fin n := ⟨t₁.1, by omega⟩
        have h₁ : cup2CycleVal n t₁.1 j.1 = 0 := by
          simpa [j] using cup2Cycle_phase1_mover_self n ht₁_phase1
        have h₂ : cup2CycleVal n t₂.1 j.1 = 1 := by
          simpa [j] using cup2Cycle_phase1_one_before_mover n ht₂_phase1 (j := t₁.1) hlt
        have hfalse : False := by
          have hval := cup2CycleConfig_eq_val n hn heq j
          rw [h₁, h₂] at hval
          omega
        exact False.elim hfalse
      · by_cases hgt : t₂.1 < t₁.1
        · let j : Fin n := ⟨t₂.1, by omega⟩
          have h₁ : cup2CycleVal n t₁.1 j.1 = 1 := by
            simpa [j] using cup2Cycle_phase1_one_before_mover n ht₁_phase1 (j := t₂.1) hgt
          have h₂ : cup2CycleVal n t₂.1 j.1 = 0 := by
            simpa [j] using cup2Cycle_phase1_mover_self n ht₂_phase1
          have hfalse : False := by
            have hval := cup2CycleConfig_eq_val n hn heq j
            rw [h₁, h₂] at hval
            omega
          exact False.elim hfalse
        · apply Fin.ext
          omega
    · let j : Fin n := ⟨n - 1, by omega⟩
      have h₁ : cup2CycleVal n t₁.1 j.1 = 0 := by
        simpa [j] using cup2Cycle_phase1_top_val n ht₁_phase1
      have h₂ : cup2CycleVal n t₂.1 j.1 = 1 := by
        simpa [j] using cup2Cycle_nonphase1_top_val n hn ht₂_phase1 t₂.2
      have hfalse : False := by
        have hval := cup2CycleConfig_eq_val n hn heq j
        rw [h₁, h₂] at hval
        omega
      exact False.elim hfalse
  · by_cases ht₂_phase1 : t₂.1 < n
    · let j : Fin n := ⟨n - 1, by omega⟩
      have h₁ : cup2CycleVal n t₁.1 j.1 = 1 := by
        simpa [j] using cup2Cycle_nonphase1_top_val n hn ht₁_phase1 t₁.2
      have h₂ : cup2CycleVal n t₂.1 j.1 = 0 := by
        simpa [j] using cup2Cycle_phase1_top_val n ht₂_phase1
      have hfalse : False := by
        have hval := cup2CycleConfig_eq_val n hn heq j
        rw [h₁, h₂] at hval
        omega
      exact False.elim hfalse
    · by_cases ht₁_phase2 : t₁.1 < 2 * n - 2
      · have ht₁n : n ≤ t₁.1 := by omega
        by_cases ht₂_phase2 : t₂.1 < 2 * n - 2
        · have ht₂n : n ≤ t₂.1 := by omega
          by_cases hlt : t₁.1 < t₂.1
          · let j : Fin n := ⟨2 * n - 1 - t₂.1, by omega⟩
            have h₁ : cup2CycleVal n t₁.1 j.1 = 1 := by
              simpa [j] using
                cup2Cycle_phase2_one_before_front n ht₁n ht₁_phase2
                  (j := 2 * n - 1 - t₂.1) (by omega)
            have h₂ : cup2CycleVal n t₂.1 j.1 = 2 := by
              simpa [j] using
                cup2Cycle_phase2_two_before_top n ht₂n ht₂_phase2
                  (j := 2 * n - 1 - t₂.1) (by omega) (by omega)
            have hfalse : False := by
              have hval := cup2CycleConfig_eq_val n hn heq j
              rw [h₁, h₂] at hval
              omega
            exact False.elim hfalse
          · by_cases hgt : t₂.1 < t₁.1
            · let j : Fin n := ⟨2 * n - 1 - t₁.1, by omega⟩
              have h₁ : cup2CycleVal n t₁.1 j.1 = 2 := by
                simpa [j] using
                  cup2Cycle_phase2_two_before_top n ht₁n ht₁_phase2
                    (j := 2 * n - 1 - t₁.1) (by omega) (by omega)
              have h₂ : cup2CycleVal n t₂.1 j.1 = 1 := by
                simpa [j] using
                  cup2Cycle_phase2_one_before_front n ht₂n ht₂_phase2
                    (j := 2 * n - 1 - t₁.1) (by omega)
              have hfalse : False := by
                have hval := cup2CycleConfig_eq_val n hn heq j
                rw [h₁, h₂] at hval
                omega
              exact False.elim hfalse
            · apply Fin.ext
              omega
        · by_cases ht₂_start : t₂.1 = 2 * n - 2
          · let j : Fin n := ⟨1, by omega⟩
            have h₁ : cup2CycleVal n t₁.1 j.1 = 1 := by
              simpa [j] using
                cup2Cycle_phase2_one_before_front n ht₁n ht₁_phase2 (j := 1) (by omega)
            have h₂ : cup2CycleVal n t₂.1 j.1 = 2 := by
              rw [ht₂_start]
              simpa [j] using cup2Cycle_phase3_start_right_input n hn
            have hfalse : False := by
              have hval := cup2CycleConfig_eq_val n hn heq j
              rw [h₁, h₂] at hval
              omega
            exact False.elim hfalse
          · by_cases ht₂_phase3 : t₂.1 < 3 * n - 3
            · have ht₂0 : 2 * n - 1 ≤ t₂.1 := by omega
              let j : Fin n := ⟨0, by omega⟩
              have h₁ : cup2CycleVal n t₁.1 j.1 = 1 := by
                simpa [j] using
                  cup2Cycle_phase2_one_before_front n ht₁n ht₁_phase2 (j := 0) (by omega)
              have h₂ : cup2CycleVal n t₂.1 j.1 = 0 := by
                simpa [j] using
                  cup2Cycle_phase3_nonstart_zero_before_mover n ht₂0 ht₂_phase3 (j := 0) (by omega)
              have hfalse : False := by
                have hval := cup2CycleConfig_eq_val n hn heq j
                rw [h₁, h₂] at hval
                omega
              exact False.elim hfalse
            · have ht₂_last : t₂.1 = 3 * n - 3 := by
                have hlt : t₂.1 < cup2CycleLen n := t₂.2
                unfold cup2CycleLen at hlt
                omega
              let j : Fin n := ⟨0, by omega⟩
              have h₁ : cup2CycleVal n t₁.1 j.1 = 1 := by
                simpa [j] using
                  cup2Cycle_phase2_one_before_front n ht₁n ht₁_phase2 (j := 0) (by omega)
              have h₂ : cup2CycleVal n t₂.1 j.1 = 0 := by
                rw [ht₂_last]
                simpa [j] using cup2Cycle_phase3_last_right_input n hn
              have hfalse : False := by
                have hval := cup2CycleConfig_eq_val n hn heq j
                rw [h₁, h₂] at hval
                omega
              exact False.elim hfalse
      · by_cases ht₁_start : t₁.1 = 2 * n - 2
        · by_cases ht₂_phase2 : t₂.1 < 2 * n - 2
          · have ht₂n : n ≤ t₂.1 := by omega
            let j : Fin n := ⟨1, by omega⟩
            have h₁ : cup2CycleVal n t₁.1 j.1 = 2 := by
              rw [ht₁_start]
              simpa [j] using cup2Cycle_phase3_start_right_input n hn
            have h₂ : cup2CycleVal n t₂.1 j.1 = 1 := by
              simpa [j] using
                cup2Cycle_phase2_one_before_front n ht₂n ht₂_phase2 (j := 1) (by omega)
            have hfalse : False := by
              have hval := cup2CycleConfig_eq_val n hn heq j
              rw [h₁, h₂] at hval
              omega
            exact False.elim hfalse
          · by_cases ht₂_start : t₂.1 = 2 * n - 2
            · apply Fin.ext
              omega
            · have ht₂_phase3_or_last : t₂.1 < 3 * n - 3 ∨ t₂.1 = 3 * n - 3 := by
                have hlt : t₂.1 < cup2CycleLen n := t₂.2
                unfold cup2CycleLen at hlt
                omega
              rcases ht₂_phase3_or_last with ht₂_phase3 | ht₂_last
              · have ht₂0 : 2 * n - 1 ≤ t₂.1 := by omega
                let j : Fin n := ⟨0, by omega⟩
                have h₁ : cup2CycleVal n t₁.1 j.1 = 1 := by
                  rw [ht₁_start]
                  simpa [j] using cup2Cycle_phase3_start_self n hn
                have h₂ : cup2CycleVal n t₂.1 j.1 = 0 := by
                  simpa [j] using
                    cup2Cycle_phase3_nonstart_zero_before_mover n ht₂0 ht₂_phase3 (j := 0) (by omega)
                have hfalse : False := by
                  have hval := cup2CycleConfig_eq_val n hn heq j
                  rw [h₁, h₂] at hval
                  omega
                exact False.elim hfalse
              · let j : Fin n := ⟨0, by omega⟩
                have h₁ : cup2CycleVal n t₁.1 j.1 = 1 := by
                  rw [ht₁_start]
                  simpa [j] using cup2Cycle_phase3_start_self n hn
                have h₂ : cup2CycleVal n t₂.1 j.1 = 0 := by
                  rw [ht₂_last]
                  simpa [j] using cup2Cycle_phase3_last_right_input n hn
                have hfalse : False := by
                  have hval := cup2CycleConfig_eq_val n hn heq j
                  rw [h₁, h₂] at hval
                  omega
                exact False.elim hfalse
        · by_cases ht₁_phase3 : t₁.1 < 3 * n - 3
          · have ht₁0 : 2 * n - 1 ≤ t₁.1 := by omega
            by_cases ht₂_phase2 : t₂.1 < 2 * n - 2
            · have ht₂n : n ≤ t₂.1 := by omega
              let j : Fin n := ⟨0, by omega⟩
              have h₁ : cup2CycleVal n t₁.1 j.1 = 0 := by
                simpa [j] using
                  cup2Cycle_phase3_nonstart_zero_before_mover n ht₁0 ht₁_phase3 (j := 0) (by omega)
              have h₂ : cup2CycleVal n t₂.1 j.1 = 1 := by
                simpa [j] using
                  cup2Cycle_phase2_one_before_front n ht₂n ht₂_phase2 (j := 0) (by omega)
              have hfalse : False := by
                have hval := cup2CycleConfig_eq_val n hn heq j
                rw [h₁, h₂] at hval
                omega
              exact False.elim hfalse
            · by_cases ht₂_start : t₂.1 = 2 * n - 2
              · let j : Fin n := ⟨0, by omega⟩
                have h₁ : cup2CycleVal n t₁.1 j.1 = 0 := by
                  simpa [j] using
                    cup2Cycle_phase3_nonstart_zero_before_mover n ht₁0 ht₁_phase3 (j := 0) (by omega)
                have h₂ : cup2CycleVal n t₂.1 j.1 = 1 := by
                  rw [ht₂_start]
                  simpa [j] using cup2Cycle_phase3_start_self n hn
                have hfalse : False := by
                  have hval := cup2CycleConfig_eq_val n hn heq j
                  rw [h₁, h₂] at hval
                  omega
                exact False.elim hfalse
              · by_cases ht₂_phase3 : t₂.1 < 3 * n - 3
                · have ht₂0 : 2 * n - 1 ≤ t₂.1 := by omega
                  by_cases hlt : t₁.1 < t₂.1
                  · let j : Fin n := ⟨t₁.1 - (2 * n - 2), by omega⟩
                    have h₁ : cup2CycleVal n t₁.1 j.1 = 2 := by
                      simpa [j] using cup2Cycle_phase3_nonstart_self n ht₁0 ht₁_phase3
                    have h₂ : cup2CycleVal n t₂.1 j.1 = 0 := by
                      simpa [j] using
                        cup2Cycle_phase3_nonstart_zero_before_mover n ht₂0 ht₂_phase3
                          (j := t₁.1 - (2 * n - 2)) (by omega)
                    have hfalse : False := by
                      have hval := cup2CycleConfig_eq_val n hn heq j
                      rw [h₁, h₂] at hval
                      omega
                    exact False.elim hfalse
                  · by_cases hgt : t₂.1 < t₁.1
                    · let j : Fin n := ⟨t₂.1 - (2 * n - 2), by omega⟩
                      have h₁ : cup2CycleVal n t₁.1 j.1 = 0 := by
                        simpa [j] using
                          cup2Cycle_phase3_nonstart_zero_before_mover n ht₁0 ht₁_phase3
                            (j := t₂.1 - (2 * n - 2)) (by omega)
                      have h₂ : cup2CycleVal n t₂.1 j.1 = 2 := by
                        simpa [j] using cup2Cycle_phase3_nonstart_self n ht₂0 ht₂_phase3
                      have hfalse : False := by
                        have hval := cup2CycleConfig_eq_val n hn heq j
                        rw [h₁, h₂] at hval
                        omega
                      exact False.elim hfalse
                    · apply Fin.ext
                      omega
                · have ht₂_last : t₂.1 = 3 * n - 3 := by
                    have hlt : t₂.1 < cup2CycleLen n := t₂.2
                    unfold cup2CycleLen at hlt
                    omega
                  let j : Fin n := ⟨t₁.1 - (2 * n - 2), by omega⟩
                  have h₁ : cup2CycleVal n t₁.1 j.1 = 2 := by
                    simpa [j] using cup2Cycle_phase3_nonstart_self n ht₁0 ht₁_phase3
                  have h₂ : cup2CycleVal n t₂.1 j.1 = 0 := by
                    rw [ht₂_last]
                    simpa [j] using
                      cup2Cycle_phase3_last_zero_before_top n hn
                        (j := t₁.1 - (2 * n - 2)) (by omega)
                  have hfalse : False := by
                    have hval := cup2CycleConfig_eq_val n hn heq j
                    rw [h₁, h₂] at hval
                    omega
                  exact False.elim hfalse
          · have ht₁_last : t₁.1 = 3 * n - 3 := by
              have hlt : t₁.1 < cup2CycleLen n := t₁.2
              unfold cup2CycleLen at hlt
              omega
            by_cases ht₂_phase2 : t₂.1 < 2 * n - 2
            · have ht₂n : n ≤ t₂.1 := by omega
              let j : Fin n := ⟨0, by omega⟩
              have h₁ : cup2CycleVal n t₁.1 j.1 = 0 := by
                rw [ht₁_last]
                simpa [j] using cup2Cycle_phase3_last_right_input n hn
              have h₂ : cup2CycleVal n t₂.1 j.1 = 1 := by
                simpa [j] using
                  cup2Cycle_phase2_one_before_front n ht₂n ht₂_phase2 (j := 0) (by omega)
              have hfalse : False := by
                have hval := cup2CycleConfig_eq_val n hn heq j
                rw [h₁, h₂] at hval
                omega
              exact False.elim hfalse
            · by_cases ht₂_start : t₂.1 = 2 * n - 2
              · let j : Fin n := ⟨0, by omega⟩
                have h₁ : cup2CycleVal n t₁.1 j.1 = 0 := by
                  rw [ht₁_last]
                  simpa [j] using cup2Cycle_phase3_last_right_input n hn
                have h₂ : cup2CycleVal n t₂.1 j.1 = 1 := by
                  rw [ht₂_start]
                  simpa [j] using cup2Cycle_phase3_start_self n hn
                have hfalse : False := by
                  have hval := cup2CycleConfig_eq_val n hn heq j
                  rw [h₁, h₂] at hval
                  omega
                exact False.elim hfalse
              · by_cases ht₂_phase3 : t₂.1 < 3 * n - 3
                · have ht₂0 : 2 * n - 1 ≤ t₂.1 := by omega
                  let j : Fin n := ⟨t₂.1 - (2 * n - 2), by omega⟩
                  have h₁ : cup2CycleVal n t₁.1 j.1 = 0 := by
                    rw [ht₁_last]
                    simpa [j] using
                      cup2Cycle_phase3_last_zero_before_top n hn
                        (j := t₂.1 - (2 * n - 2)) (by omega)
                  have h₂ : cup2CycleVal n t₂.1 j.1 = 2 := by
                    simpa [j] using cup2Cycle_phase3_nonstart_self n ht₂0 ht₂_phase3
                  have hfalse : False := by
                    have hval := cup2CycleConfig_eq_val n hn heq j
                    rw [h₁, h₂] at hval
                    omega
                  exact False.elim hfalse
                · have ht₂_last : t₂.1 = 3 * n - 3 := by
                    have hlt : t₂.1 < cup2CycleLen n := t₂.2
                    unfold cup2CycleLen at hlt
                    omega
                  apply Fin.ext
                  omega

def cup2GoodCycleOfUniquePrivileged (n : Nat) (hn : 4 ≤ n)
    (huniq :
      ∀ t : Fin (cup2CycleLen n),
        ∃! i, privileged (cup2System n hn) (cup2CycleConfig n hn t) i) :
    GoodCycle (cup2System n hn) where
  configs := cup2CycleConfigs n hn
  nonempty := by
    apply List.length_pos_iff_ne_nil.mp
    rw [cup2CycleConfigs_length]
    have hn0 : 0 < n := by
      omega
    unfold cup2CycleLen
    omega
  unique_privileged := by
    intro c hc
    rcases (List.mem_ofFn.mp (by simpa [cup2CycleConfigs] using hc)) with ⟨t, rfl⟩
    exact huniq t
  closed := cup2Cycle_closed_step n hn
  distinct := by
    intro j₁ j₂ hget
    let t₁ : Fin (cup2CycleLen n) := ⟨j₁.1, by simpa [cup2CycleConfigs] using j₁.2⟩
    let t₂ : Fin (cup2CycleLen n) := ⟨j₂.1, by simpa [cup2CycleConfigs] using j₂.2⟩
    have hcfg : cup2CycleConfig n hn t₁ = cup2CycleConfig n hn t₂ := by
      simpa [cup2CycleConfigs, t₁, t₂] using hget
    have ht : t₁ = t₂ := cup2CycleConfig_injective n hn hcfg
    apply Fin.ext
    simpa [t₁, t₂] using congrArg Fin.val ht
  fair := by
    -- Every processor fires at least once: processor i fires at step i (phase 1).
    -- The cup2 cycle has phases: phase 1 visits processors 0,1,...,n-1 in order.
    intro i
    have hi_lt : i.1 < cup2CycleLen n := lt_cup2CycleLen_of_lt_n n hn i.2
    let k : Fin (cup2CycleConfigs n hn).length := ⟨i.1, by
      rw [cup2CycleConfigs_length]; exact hi_lt⟩
    let t : Fin (cup2CycleLen n) := ⟨i.1, hi_lt⟩
    have hk : (cup2CycleConfigs n hn).get k = cup2CycleConfig n hn t := by
      simpa [t] using cup2CycleConfigs_get_eq n hn k
    have hkNext :
        (cup2CycleConfigs n hn).get (nextIndex (cup2CycleConfigs n hn) k) =
          cup2CycleConfig n hn (cup2CycleNext n t) := by
      simpa [t] using cup2CycleConfigs_get_next_eq n hn k
    -- Witness: processor i fires at step k = i
    refine ⟨k, cup2Phase1Mover n i.1 i.2, ?_, ?_, Fin.ext rfl⟩
    · -- Processor i is privileged at config k (phase 1, step i)
      rw [hk]
      simpa [cup2Phase1Config] using cup2Cycle_phase1_privileged n hn i.2
    · -- The move at processor i produces the next config
      rw [hk, hkNext, cup2CycleNext_phase1 n hn i.2]
      simpa [cup2Phase1Config] using (cup2Cycle_phase1_step n hn i.2).symm

theorem cup2Cycle_singlePrivileged (n : Nat) (hn : 4 ≤ n) (t : Fin (cup2CycleLen n)) :
    ∃! i, privileged (cup2System n hn) (cup2CycleConfig n hn t) i := by
  by_cases ht1 : t.1 < n
  · simpa [cup2Phase1Config] using cup2Cycle_phase1_singlePrivileged n hn ht1
  · by_cases ht2 : t.1 < 2 * n - 2
    · have htn : n ≤ t.1 := by
        omega
      simpa [cup2Phase2Config] using cup2Cycle_phase2_singlePrivileged n hn htn ht2
    · by_cases hstart : t.1 = 2 * n - 2
      · have htEq :
            t = ⟨2 * n - 2,
              lt_cup2CycleLen_of_phase3_interior n hn (by omega) (by omega)⟩ := by
          ext
          simpa using hstart
        rw [htEq]
        simpa [cup2Phase3StartConfig, cup2Phase3Config] using
          cup2Cycle_phase3_start_singlePrivileged n hn
      · by_cases hphase3 : t.1 < 3 * n - 3
        · have ht0 : 2 * n - 1 ≤ t.1 := by
            omega
          simpa [cup2Phase3Config] using
            cup2Cycle_phase3_nonstart_singlePrivileged n hn ht0 hphase3
        · have hlast : t.1 = 3 * n - 3 := by
            have hlt : t.1 < cup2CycleLen n := t.2
            unfold cup2CycleLen at hlt
            omega
          have htEq : t = ⟨3 * n - 3, phase3_last_lt n hn⟩ := by
            ext
            simpa using hlast
          rw [htEq]
          simpa [cup2Phase3LastConfig, cup2Phase3Config] using
            cup2Cycle_phase3_last_singlePrivileged n hn

def cup2GoodCycle (n : Nat) (hn : 4 ≤ n) : GoodCycle (cup2System n hn) :=
  cup2GoodCycleOfUniquePrivileged n hn (cup2Cycle_singlePrivileged n hn)

end MoverProofs

end LeanMn
