/-
  PhaseExtractionBase.lean — Phase extraction infrastructure

  TernaryPhase extraction, mechanism dispatch, normal form classification,
  firing support analysis, outside-step suffix lemmas, and zero set reduction.
-/
import LeanMn.LowerBound.EntryConflict.TernaryPhaseEC
import LeanMn.LowerBound.EntryConflict.NonConsecutive
import LeanMn.LowerBound.EntryConflict.BinaryRightCrossing
import LeanMn.LowerBound.EntryConflict.BAFWord
import LeanMn.LowerBound.FireCountNe
import LeanMn.LowerBound.Shadow.Theorem

namespace LeanMn

variable {sys : System}

/-! ### Step 1: Sandwiched ternary extraction -/

/-- On a ring with a binary-gap-binary pattern and sub-threshold product,
    there exists a ternary processor t with both left(t) and right(t) binary.

    The hypothesis `hgap` directly asserts the pattern: some processor i is
    binary, right(right(i)) is binary, and right(i) is ternary (gap of size 1).
    This pattern must be established by the ring-level cluster/gap analysis.

    Note: The hypotheses (≥3 binary + no 3 consecutive + n ≥ 7) alone do NOT
    suffice — e.g., 3 binary equally spaced on a 9-ring has all gaps ≥ 2. -/
theorem exists_ternary_sandwiched_between_binary
    (rs : RingSpec) (_hn : rs.n ≥ 9)
    (_hsub : subThreshold rs)
    (_h3bin : hasGe3Binary rs)
    (_hnoncons : ¬∃ i : Fin rs.n, threeConsecutiveBinary rs i)
    (hgap : ∃ i : Fin rs.n,
      isBinary rs i ∧ ¬isBinary rs (right i) ∧ isBinary rs (right (right i)) ∧
      isTernary rs (right i)) :
    ∃ t : Fin rs.n,
      isTernary rs t ∧ isBinary rs (left t) ∧ isBinary rs (right t) := by
  obtain ⟨i, hibin, _, hrribin, hri_tern⟩ := hgap
  refine ⟨right i, hri_tern, ?_, hrribin⟩
  rw [left_right_eq_self]; exact hibin

/-! ### Step 2: Phase interval extraction -/

/-- A ternary phase: processor t fires at step s, and doesn't fire in [a, s).
    Steps a and s are both valid indices into gc.configs. -/
structure TernaryPhase (gc : GoodCycle sys) (t : Fin sys.rs.n) where
  a : Fin gc.configs.length
  s : Fin gc.configs.length
  ha_lt_s : a.val < s.val
  hs_mover : gc.moverAt s = t
  ha_nonmover : gc.moverAt a ≠ t
  ht_nofire : ∀ k : Fin gc.configs.length,
    a.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ t

/-- Any suffix of a ternary phase is again a ternary phase, as long as the
    new start step is still a non-mover for `t`. This packages the common
    "start later in the same gap" construction used in suffix-normal arguments. -/
private def TernaryPhase.suffix
    {gc : GoodCycle sys} {t : Fin sys.rs.n}
    (phase : TernaryPhase gc t)
    (a' : Fin gc.configs.length)
    (ha' : phase.a.val ≤ a'.val)
    (ha'_lt_s : a'.val < phase.s.val)
    (ha'_nonmover : gc.moverAt a' ≠ t) :
    TernaryPhase gc t where
  a := a'
  s := phase.s
  ha_lt_s := ha'_lt_s
  hs_mover := phase.hs_mover
  ha_nonmover := ha'_nonmover
  ht_nofire := fun k hk1 hk2 => phase.ht_nofire k (le_trans ha' hk1) hk2

/-- The suffix phase is strictly shorter if its start is strictly later. -/
private theorem TernaryPhase.suffix_len_lt
    {gc : GoodCycle sys} {t : Fin sys.rs.n}
    (phase : TernaryPhase gc t)
    (a' : Fin gc.configs.length)
    (ha' : phase.a.val ≤ a'.val)
    (ha'_lt_s : a'.val < phase.s.val)
    (ha'_nonmover : gc.moverAt a' ≠ t)
    (hstrict : phase.a.val < a'.val) :
    phase.s.val - (phase.suffix a' ha' ha'_lt_s ha'_nonmover).a.val <
      phase.s.val - phase.a.val := by
  simp [TernaryPhase.suffix]
  omega

/-! #### Helper: extract two distinct firing steps from fireCount ≥ 2 -/

theorem exists_two_fire_steps_of_ge2 (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hfc : gc.fireCount t ≥ 2) :
    ∃ (a b : Fin gc.configs.length), a.val < b.val ∧
      gc.moverAt a = t ∧ gc.moverAt b = t := by
  have hexists1 : ∃ a : Fin gc.configs.length, gc.moverAt a = t := by
    by_contra hall; push_neg at hall
    have hzero : gc.fireCount t = 0 := by
      rw [gc.fireCount_eq_sum_moverAt t]
      apply Finset.sum_eq_zero
      intro j _; simp [show gc.moverAt j ≠ t from hall j]
    omega
  obtain ⟨a, ha⟩ := hexists1
  have hexists2 : ∃ b : Fin gc.configs.length, b ≠ a ∧ gc.moverAt b = t := by
    by_contra hall; push_neg at hall
    have hle1 : gc.fireCount t ≤ 1 := by
      rw [gc.fireCount_eq_sum_moverAt t]
      have hbd : ∀ j : Fin gc.configs.length,
          (if gc.moverAt j = t then (1 : Nat) else 0) ≤ (if j = a then 1 else 0) := by
        intro j
        by_cases hja : j = a
        · rw [hja]; simp [ha]
        · have : gc.moverAt j ≠ t := hall j hja; simp [this]
      calc ∑ j : Fin gc.configs.length, (if gc.moverAt j = t then (1 : Nat) else 0)
          ≤ ∑ j : Fin gc.configs.length, (if j = a then (1 : Nat) else 0) :=
            Finset.sum_le_sum (fun j _ => hbd j)
        _ = 1 := by
            rw [Finset.sum_eq_single a
              (fun b _ hba => by simp [hba]) (by simp)]; simp
    omega
  obtain ⟨b, hne, hb⟩ := hexists2
  have hne_val : a.val ≠ b.val := fun h => hne (Fin.ext h).symm
  by_cases hab : a.val < b.val
  · exact ⟨a, b, hab, ha, hb⟩
  · exact ⟨b, a, by omega, hb, ha⟩

/-! #### Helper: refine to consecutive firing pair -/

private theorem exists_consecutive_fire_pair (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (a b : Fin gc.configs.length) (hab : a.val < b.val)
    (ha : gc.moverAt a = t) (hb : gc.moverAt b = t) :
    ∃ (a' b' : Fin gc.configs.length),
      a'.val < b'.val ∧ gc.moverAt a' = t ∧ gc.moverAt b' = t ∧
      (∀ k : Fin gc.configs.length,
        a'.val < k.val → k.val < b'.val → gc.moverAt k ≠ t) := by
  suffices hmain : ∀ d : Nat, ∀ (a b : Fin gc.configs.length),
      b.val - a.val ≤ d → a.val < b.val →
      gc.moverAt a = t → gc.moverAt b = t →
      ∃ (a' b' : Fin gc.configs.length),
        a'.val < b'.val ∧ gc.moverAt a' = t ∧ gc.moverAt b' = t ∧
        (∀ k : Fin gc.configs.length,
          a'.val < k.val → k.val < b'.val → gc.moverAt k ≠ t) by
    exact hmain (b.val - a.val) a b le_rfl hab ha hb
  intro d
  induction d with
  | zero => intro a b hd hab; omega
  | succ d ih =>
    intro a b hd hab ha hb
    by_cases hno : ∀ k : Fin gc.configs.length,
        a.val < k.val → k.val < b.val → gc.moverAt k ≠ t
    · exact ⟨a, b, hab, ha, hb, hno⟩
    · push_neg at hno
      obtain ⟨k, hak, hkb, hk⟩ := hno
      exact ih k b (by omega) hkb hk hb

/-- Variant of `exists_consecutive_fire_pair` with explicit bounds:
    the returned pair satisfies a ≤ a' and b' ≤ b. -/
private theorem exists_consecutive_fire_pair_bounded (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (a b : Fin gc.configs.length) (hab : a.val < b.val)
    (ha : gc.moverAt a = t) (hb : gc.moverAt b = t) :
    ∃ (a' b' : Fin gc.configs.length),
      a.val ≤ a'.val ∧ b'.val ≤ b.val ∧
      a'.val < b'.val ∧ gc.moverAt a' = t ∧ gc.moverAt b' = t ∧
      (∀ k : Fin gc.configs.length,
        a'.val < k.val → k.val < b'.val → gc.moverAt k ≠ t) := by
  suffices hmain : ∀ d : Nat, ∀ (a b : Fin gc.configs.length),
      b.val - a.val ≤ d → a.val < b.val →
      gc.moverAt a = t → gc.moverAt b = t →
      ∃ (a' b' : Fin gc.configs.length),
        a.val ≤ a'.val ∧ b'.val ≤ b.val ∧
        a'.val < b'.val ∧ gc.moverAt a' = t ∧ gc.moverAt b' = t ∧
        (∀ k : Fin gc.configs.length,
          a'.val < k.val → k.val < b'.val → gc.moverAt k ≠ t) by
    exact hmain (b.val - a.val) a b le_rfl hab ha hb
  intro d
  induction d with
  | zero => intro a b hd hab; omega
  | succ d ih =>
    intro a b hd hab ha hb
    by_cases hno : ∀ k : Fin gc.configs.length,
        a.val < k.val → k.val < b.val → gc.moverAt k ≠ t
    · exact ⟨a, b, le_rfl, le_rfl, hab, ha, hb, hno⟩
    · push_neg at hno
      obtain ⟨k, hak, hkb, hk⟩ := hno
      obtain ⟨a', b', hka', hb'b, hab', ha', hb', hno'⟩ :=
        ih k b (by omega) hkb hk hb
      exact ⟨a', b', by omega, hb'b, hab', ha', hb', hno'⟩

/-- If processor t fires at least twice and there exists a step where t
    does not fire, then there exists a TernaryPhase for t. -/
theorem exists_ternaryPhase (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hfc_ge2 : gc.fireCount t ≥ 2)
    (hfc_lt_L : gc.fireCount t < gc.configs.length) :
    ∃ phase : TernaryPhase gc t, True := by
  classical
  have hL_pos := gc.configs_length_pos
  -- There exists a step where t fires
  have hexists_fire : ∃ k : Fin gc.configs.length, gc.moverAt k = t := by
    by_contra hall; push_neg at hall
    have : gc.fireCount t = 0 := by
      rw [gc.fireCount_eq_sum_moverAt t]
      apply Finset.sum_eq_zero; intro j _; simp [hall j]
    omega
  -- Case: step 0 does not fire
  by_cases h0fire : gc.moverAt ⟨0, hL_pos⟩ = t
  · -- Step 0 fires. Look for a fire step s > 0 preceded by a non-fire step.
    by_cases hgood : ∃ (s : Fin gc.configs.length),
        s.val > 0 ∧ gc.moverAt s = t ∧
        gc.moverAt ⟨s.val - 1, by have := s.isLt; omega⟩ ≠ t
    · obtain ⟨s, hs_pos, hs_fire, hs_pred_nonfire⟩ := hgood
      have hs_lt := s.isLt
      have hpred_lt : s.val - 1 < gc.configs.length := by omega
      have hpred_lt_s : s.val - 1 < s.val := by omega
      refine ⟨⟨⟨s.val - 1, hpred_lt⟩, s, hpred_lt_s, hs_fire, hs_pred_nonfire,
        fun k hk1 hk2 => ?_⟩, trivial⟩
      have hk1' : s.val - 1 ≤ k.val := hk1
      have hkeq : k.val = s.val - 1 := by omega
      have : k = ⟨s.val - 1, hpred_lt⟩ := Fin.ext hkeq
      rw [this]; exact hs_pred_nonfire
    · -- Every fire step s > 0 has s-1 also firing → fires form prefix [0, fc).
      push_neg at hgood
      exfalso
      have hdescend : ∀ (s : Fin gc.configs.length),
          gc.moverAt s = t → ∀ (j : Fin gc.configs.length),
          j.val ≤ s.val → gc.moverAt j = t := by
        intro s hs j hjs
        suffices hmain : ∀ (n : Nat) (s' : Fin gc.configs.length),
            gc.moverAt s' = t → s'.val = j.val + n → gc.moverAt j = t by
          exact hmain (s.val - j.val) s hs (by omega)
        intro n
        induction n with
        | zero =>
          intro s' hs' heq
          have : j = s' := Fin.ext (by omega)
          rw [this]; exact hs'
        | succ n ih =>
          intro s' hs' heq
          have hs'_pos : s'.val > 0 := by omega
          have hpred := hgood s' hs'_pos hs'
          have hs'_lt := s'.isLt
          have : s'.val - 1 = j.val + n := by omega
          exact ih ⟨s'.val - 1, by omega⟩ hpred this
      have hfire_prefix : ∀ (k : Nat) (hk : k < gc.configs.length),
          k < gc.fireCount t → gc.moverAt ⟨k, hk⟩ = t := by
        intro k hk hkfc
        by_contra hno
        have hnofire_ge_k : ∀ (m : Nat) (hm : m < gc.configs.length), k ≤ m →
            gc.moverAt ⟨m, hm⟩ ≠ t := by
          intro m hm hkm hmov
          exact hno (hdescend ⟨m, hm⟩ hmov ⟨k, hk⟩ hkm)
        have hnofire_interval : gc.intervalFireCount t k gc.configs.length = 0 := by
          apply intervalFireCount_eq_zero_of_noFire gc t (by omega) le_rfl
          intro j hj1 hj2
          exact hnofire_ge_k j.val j.isLt hj1
        have hfc_eq_pfc : gc.fireCount t = gc.prefixFireCount t k := by
          have hdef : gc.intervalFireCount t k gc.configs.length =
            gc.prefixFireCount t gc.configs.length - gc.prefixFireCount t k := rfl
          rw [hnofire_interval] at hdef
          have hmono : gc.prefixFireCount t k ≤ gc.prefixFireCount t gc.configs.length := by
            unfold GoodCycle.prefixFireCount
            exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
          unfold GoodCycle.fireCount
          omega
        have hpfc_le : gc.prefixFireCount t k ≤ k := by
          unfold GoodCycle.prefixFireCount
          calc ∑ i ∈ Finset.range k, gc.fireIndicator t i
              ≤ ∑ _i ∈ Finset.range k, 1 :=
                Finset.sum_le_sum fun i _ => by
                  unfold GoodCycle.fireIndicator; split_ifs <;> omega
            _ = k := by simp
        omega
      have hnofire_after : ∀ (k : Nat) (hk : k < gc.configs.length),
          gc.fireCount t ≤ k → gc.moverAt ⟨k, hk⟩ ≠ t := by
        intro k hk hge hmk
        have hall : ∀ j : Fin gc.configs.length, j.val ≤ k →
            gc.moverAt j = t :=
          fun j hle => hdescend ⟨k, hk⟩ hmk j hle
        have hpfc : ∀ m : Nat, m ≤ k + 1 → m ≤ gc.configs.length →
            (∀ j : Fin gc.configs.length, j.val < m → gc.moverAt j = t) →
            gc.prefixFireCount t m = m := by
          intro m
          induction m with
          | zero => intro _ _ _; simp [GoodCycle.prefixFireCount]
          | succ m ih =>
            intro hm hml hfire
            rw [gc.prefixFireCount_succ]
            have hm_lt : m < gc.configs.length := by omega
            have hmov := hfire ⟨m, hm_lt⟩ (show m < m + 1 by omega)
            simp [GoodCycle.fireIndicator, hm_lt, hmov]
            exact ih (by omega) (by omega) (fun j (hj : j.val < m) => hfire j (by omega))
        have hpfc_val : gc.prefixFireCount t (k + 1) = k + 1 :=
          hpfc (k + 1) le_rfl (by omega) (fun j hj => hall j (by omega : j.val ≤ k))
        have : gc.prefixFireCount t (k + 1) ≤ gc.fireCount t := by
          unfold GoodCycle.fireCount
          exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
        omega
      have hfc_pos : gc.fireCount t > 0 := by omega
      have hcfg_eq_nont : ∀ (q : Fin sys.rs.n), q ≠ t →
          (gc.configs.get ⟨0, hL_pos⟩) q =
          (gc.configs.get ⟨gc.fireCount t, hfc_lt_L⟩) q := by
        intro q hq
        exact configVal_eq_of_noFire_between gc q 0 (gc.fireCount t) (Nat.zero_le _) hfc_lt_L
          fun k hk1 hk2 => by
            have := hfire_prefix k.val k.isLt hk2
            intro habs; rw [habs] at this; exact hq this
      have hcfg_eq_t_partial : gc.fireCount t < gc.configs.length - 1 →
          (gc.configs.get ⟨gc.fireCount t, hfc_lt_L⟩) t =
          (gc.configs.get ⟨gc.configs.length - 1, by omega⟩) t := by
        intro hfc_lt
        exact configVal_eq_of_noFire_between gc t (gc.fireCount t) (gc.configs.length - 1)
          (by omega) (by omega)
          fun k hk1 hk2 => hnofire_after k.val k.isLt (by omega)
      have hwrap : (gc.configs.get ⟨gc.configs.length - 1, by omega⟩) t =
          (gc.configs.get ⟨0, hL_pos⟩) t := by
        have hL1_lt := show gc.configs.length - 1 < gc.configs.length by omega
        have hmov_L1 := hnofire_after (gc.configs.length - 1) hL1_lt (by omega)
        have ht_ne : t ≠ gc.moverAt ⟨gc.configs.length - 1, hL1_lt⟩ := fun h => hmov_L1 h.symm
        have hstep := gc.state_eq_of_ne_moverAt ⟨gc.configs.length - 1, hL1_lt⟩ t ht_ne
        have hnext : nextIndex gc.configs ⟨gc.configs.length - 1, hL1_lt⟩ = ⟨0, hL_pos⟩ := by
          ext; simp [nextIndex]
          show (gc.configs.length - 1 + 1) % gc.configs.length = 0
          rw [show gc.configs.length - 1 + 1 = gc.configs.length from by omega]
          exact Nat.mod_self _
        rw [hnext] at hstep
        exact hstep.symm
      have hcfg_eq_t : (gc.configs.get ⟨gc.fireCount t, hfc_lt_L⟩) t =
          (gc.configs.get ⟨0, hL_pos⟩) t := by
        by_cases hfc_eq : gc.fireCount t = gc.configs.length - 1
        · have hfin_eq : (⟨gc.fireCount t, hfc_lt_L⟩ : Fin gc.configs.length) =
              ⟨gc.configs.length - 1, by omega⟩ := Fin.ext hfc_eq
          calc (gc.configs.get ⟨gc.fireCount t, hfc_lt_L⟩) t
              = (gc.configs.get ⟨gc.configs.length - 1, by omega⟩) t := by
                rw [show (⟨gc.fireCount t, hfc_lt_L⟩ : Fin gc.configs.length) =
                  ⟨gc.configs.length - 1, by omega⟩ from hfin_eq]
            _ = (gc.configs.get ⟨0, hL_pos⟩) t := hwrap
        · have hfc_lt' : gc.fireCount t < gc.configs.length - 1 := by omega
          calc (gc.configs.get ⟨gc.fireCount t, hfc_lt_L⟩) t
              = (gc.configs.get ⟨gc.configs.length - 1, by omega⟩) t :=
                hcfg_eq_t_partial hfc_lt'
            _ = (gc.configs.get ⟨0, hL_pos⟩) t := hwrap
      have hconfig_eq : gc.configs.get ⟨0, hL_pos⟩ =
          gc.configs.get ⟨gc.fireCount t, hfc_lt_L⟩ := by
        funext q
        by_cases hq : q = t
        · rw [hq]; exact hcfg_eq_t.symm
        · exact hcfg_eq_nont q hq
      have := gc.distinct ⟨0, hL_pos⟩ ⟨gc.fireCount t, hfc_lt_L⟩ hconfig_eq
      exact absurd (congrArg Fin.val this) (by simp; omega)
  · -- Step 0 does NOT fire. Find the minimum fire step.
    let fireSet : Finset (Fin gc.configs.length) :=
      Finset.univ.filter (fun k => gc.moverAt k = t)
    have hne : fireSet.Nonempty := by
      obtain ⟨k, hk⟩ := hexists_fire
      exact ⟨k, by simp [fireSet]; exact hk⟩
    obtain ⟨s_min, hs_min_mem, hs_min_le⟩ := Finset.exists_min_image fireSet Fin.val hne
    simp [fireSet] at hs_min_mem
    have hs_pos : s_min.val > 0 := by
      by_contra h; push_neg at h
      have : s_min.val = 0 := by omega
      have : s_min = ⟨0, hL_pos⟩ := Fin.ext this
      rw [this] at hs_min_mem; exact h0fire hs_min_mem
    have hnofire_before : ∀ k : Fin gc.configs.length,
        (0 : Nat) ≤ k.val → k.val < s_min.val → gc.moverAt k ≠ t := by
      intro k _ hk_lt hmov
      have : k ∈ fireSet := by simp [fireSet]; exact hmov
      have := hs_min_le k this; omega
    exact ⟨⟨⟨0, hL_pos⟩, s_min, hs_pos, hs_min_mem, h0fire,
      fun k hk1 hk2 => hnofire_before k (Nat.zero_le _) hk2⟩, trivial⟩

/-- If t fires at least once and fireCount ≠ 1, then fireCount ≥ 2. -/
theorem fireCount_ge_2_of_pos (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hfc_pos : gc.fireCount t > 0) :
    gc.fireCount t ≥ 2 := by
  have h1 := gc.fireCount_ne_one t
  omega

/-- For ternary processors, fire count ≥ 2 suffices for all mechanisms. -/
theorem ternary_fireCount_ge_2 (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (_htern : isTernary sys.rs t) (hfc_pos : gc.fireCount t > 0) :
    gc.fireCount t ≥ 2 :=
  fireCount_ge_2_of_pos gc t hfc_pos

/-! ### Step 3: Phase fire count classification and mechanism dispatch -/

/-- **Both-Even dispatch**: If J and K are both even in a ternary phase,
    apply bothEvenReturn_ec to get an entry conflict. -/
theorem phase_bothEven_ec (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hbL : sys.rs.m (left t) = 2)
    (hbR : sys.rs.m (right t) = 2)
    (hJ_even : Even (gc.intervalFireCount (left t) phase.a.val phase.s.val))
    (hK_even : Even (gc.intervalFireCount (right t) phase.a.val phase.s.val)) :
    hasEntryConflict gc :=
  bothEvenReturn_ec gc t phase.a phase.s phase.ha_lt_s
    phase.hs_mover phase.ha_nonmover phase.ht_nofire
    hbL hbR hJ_even hK_even

/-! ### Step 3.5: Helpers for interval fire step extraction -/

/-- If `intervalFireCount p a b ≥ 1`, there exists a step in `[a, b)` where `p` fires. -/
theorem exists_fire_step_in_interval (gc : GoodCycle sys) (p : Fin sys.rs.n)
    {a b : Nat} (hab : a ≤ b) (hb : b ≤ gc.configs.length)
    (hpos : gc.intervalFireCount p a b ≥ 1) :
    ∃ k : Fin gc.configs.length, a ≤ k.val ∧ k.val < b ∧ gc.moverAt k = p := by
  by_contra hall; push_neg at hall
  have hzero : gc.intervalFireCount p a b = 0 :=
    intervalFireCount_eq_zero_of_noFire gc p hab hb (fun k hk1 hk2 => hall k hk1 hk2)
  omega

/-- prefixFireCount splitting. -/
theorem intervalFireCount_split (gc : GoodCycle sys) (p : Fin sys.rs.n)
    {a c b : Nat} (hac : a ≤ c) (hcb : c ≤ b) :
    gc.intervalFireCount p a b =
      gc.intervalFireCount p a c + gc.intervalFireCount p c b := by
  unfold GoodCycle.intervalFireCount
  have h1 : gc.prefixFireCount p c ≥ gc.prefixFireCount p a := by
    unfold GoodCycle.prefixFireCount
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hac)
  have h2 : gc.prefixFireCount p b ≥ gc.prefixFireCount p c := by
    unfold GoodCycle.prefixFireCount
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hcb)
  omega

/-- intervalFireCount for a single step. -/
theorem intervalFireCount_single (gc : GoodCycle sys) (p : Fin sys.rs.n)
    {k : Nat} (hk : k < gc.configs.length) :
    gc.intervalFireCount p k (k + 1) =
      if gc.moverAt ⟨k, hk⟩ = p then 1 else 0 := by
  unfold GoodCycle.intervalFireCount GoodCycle.prefixFireCount
  rw [Finset.sum_range_succ]
  simp [GoodCycle.fireIndicator, hk]

/-- If step `a` is a non-`t` mover and some later step fires `t`, then there is
    a ternary phase for `t` that starts exactly at `a` and ends at the first
    later `t`-fire. -/
theorem exists_ternaryPhase_starting_at
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (a : Fin gc.configs.length)
    (ha_nonmover : gc.moverAt a ≠ t)
    (hafter : ∃ s : Fin gc.configs.length, a.val < s.val ∧ gc.moverAt s = t) :
    ∃ phase : TernaryPhase gc t, phase.a = a := by
  classical
  let fireSet : Finset (Fin gc.configs.length) :=
    (Finset.univ : Finset (Fin gc.configs.length)).filter
      (fun s => a.val < s.val ∧ gc.moverAt s = t)
  have hne : fireSet.Nonempty := by
    rcases hafter with ⟨s, hs_gt, hs_fire⟩
    have hs_gt_fin : a < s := hs_gt
    refine ⟨s, by simp [fireSet, hs_gt_fin, hs_fire]⟩
  let s : Fin gc.configs.length := fireSet.min' hne
  have hs_mem : s ∈ fireSet := Finset.min'_mem fireSet hne
  have hs_gt : a.val < s.val := by
    simp [fireSet] at hs_mem
    exact hs_mem.1
  have hs_fire : gc.moverAt s = t := by
    simp [fireSet] at hs_mem
    exact hs_mem.2
  refine ⟨{
    a := a
    s := s
    ha_lt_s := hs_gt
    hs_mover := hs_fire
    ha_nonmover := ha_nonmover
    ht_nofire := ?_
  }, rfl⟩
  intro k hk1 hk2
  by_cases hka : k = a
  · simpa [hka] using ha_nonmover
  · have hgt : a.val < k.val := by omega
    intro hk_fire
    have hgt_fin : a < k := hgt
    have hk_mem : k ∈ fireSet := by
      simp [fireSet, hgt_fin, hk_fire]
    have hs_le_k : s ≤ k := Finset.min'_le fireSet k hk_mem
    omega

/-- If `intervalFireCount p a b = 0`, then `p` does not fire at any step in `[a, b)`. -/
private theorem noFire_of_intervalFireCount_zero (gc : GoodCycle sys) (p : Fin sys.rs.n)
    {a b : Nat} (hab : a ≤ b) (_hb : b ≤ gc.configs.length)
    (hzero : gc.intervalFireCount p a b = 0) :
    ∀ k : Fin gc.configs.length, a ≤ k.val → k.val < b → gc.moverAt k ≠ p := by
  intro k hka hkb hmov
  have hone : gc.intervalFireCount p k.val (k.val + 1) = 1 := by
    rw [intervalFireCount_single gc p k.isLt]; simp [hmov]
  have hsplit1 := intervalFireCount_split gc p (show a ≤ k.val from hka) (show k.val ≤ b by omega)
  have hsplit2 := intervalFireCount_split gc p (show k.val ≤ k.val + 1 by omega) (show k.val + 1 ≤ b by omega)
  rw [hsplit1, hsplit2, hone] at hzero
  omega

/-- At two consecutive fire steps of a binary processor (no fires between),
    the processor has distinct values. -/
private theorem binary_distinct_at_consecutive_fires (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hbin : sys.rs.m p = 2)
    (k₁ k₂ : Fin gc.configs.length) (hlt : k₁.val < k₂.val)
    (hk₁ : gc.moverAt k₁ = p)
    (hnofire : ∀ k : Fin gc.configs.length,
      k₁.val < k.val → k.val < k₂.val → gc.moverAt k ≠ p) :
    (gc.configs.get k₁) p ≠ (gc.configs.get k₂) p := by
  intro heq
  have hk₁_lt := k₁.isLt
  have hk₂_lt := k₂.isLt
  -- intervalFireCount p (k₁+1) k₂ = 0 (no fires between)
  have hnofire_after : gc.intervalFireCount p (k₁.val + 1) k₂.val = 0 :=
    intervalFireCount_eq_zero_of_noFire gc p (by omega) (by omega)
      fun k hk1 hk2 => hnofire k (by omega) hk2
  -- Split: ifc(k₁, k₂) = ifc(k₁, k₁+1) + ifc(k₁+1, k₂) = 1 + 0 = 1
  have hsplit := intervalFireCount_split gc p (show k₁.val ≤ k₁.val + 1 by omega)
    (show k₁.val + 1 ≤ k₂.val by omega)
  have hone : gc.intervalFireCount p k₁.val (k₁.val + 1) = 1 := by
    rw [intervalFireCount_single gc p hk₁_lt]; simp [hk₁]
  rw [hnofire_after, hone] at hsplit
  -- intervalFireCount = 1, odd, but equal configs means even parity
  have hsa₁ : gc.stateAfter p k₁.val = (gc.configs.get k₁) p := gc.stateAfter_of_lt p hk₁_lt
  have hsa₂ : gc.stateAfter p k₂.val = (gc.configs.get k₂) p := gc.stateAfter_of_lt p hk₂_lt
  have hsa_eq : gc.stateAfter p k₁.val = gc.stateAfter p k₂.val := by rw [hsa₁, hsa₂, heq]
  rw [gc.binary_stateAfter_eq_iff_prefixFireCount_modEq p hbin
    (Nat.le_of_lt (lt_of_lt_of_le hlt (Nat.le_of_lt hk₂_lt)))
    (Nat.le_of_lt hk₂_lt)] at hsa_eq
  have hmono : gc.prefixFireCount p k₁.val ≤ gc.prefixFireCount p k₂.val := by
    unfold GoodCycle.prefixFireCount
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_of_lt hlt))
  have heven : Even (gc.intervalFireCount p k₁.val k₂.val) := by
    rw [Nat.even_iff]
    unfold GoodCycle.intervalFireCount
    -- hsa_eq : pfc k₁ % 2 = pfc k₂ % 2, hmono : pfc k₁ ≤ pfc k₂
    -- Need: (pfc k₂ - pfc k₁) % 2 = 0
    set a' := gc.prefixFireCount p k₁.val with ha'_def
    set b' := gc.prefixFireCount p k₂.val with hb'_def
    -- a' ≤ b' from hmono, a' % 2 = b' % 2 from hsa_eq
    -- Write b' = a' + (b' - a'), then (b' - a') % 2 = 0
    have hab' : a' ≤ b' := hmono
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab'
    rw [hd, Nat.add_sub_cancel_left]
    -- From hsa_eq: (a' + d) % 2 = a' % 2
    rw [hd, Nat.add_mod] at hsa_eq
    omega
  have hodd : ¬Even (gc.intervalFireCount p k₁.val k₂.val) := by
    rw [Nat.even_iff, hsplit]; omega
  exact hodd heven

/-- **Both-Silent dispatch**: If J = 0 and K = 0 in a ternary phase,
    derive an entry conflict. Both neighbors are silent in [a, s), so
    all three context values (left, self, right) are preserved, giving
    matching contexts at the non-mover step a and mover step s.
    Unlike bothEvenReturn_ec, this does NOT require both neighbors to be binary. -/
theorem phase_bothSilent_ec (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hJ_zero : gc.intervalFireCount (left t) phase.a.val phase.s.val = 0)
    (hK_zero : gc.intervalFireCount (right t) phase.a.val phase.s.val = 0) :
    hasEntryConflict gc := by
  have ha_lt_s := phase.ha_lt_s
  have hJ_nofire := noFire_of_intervalFireCount_zero gc (left t)
    (Nat.le_of_lt ha_lt_s) (le_of_lt phase.s.isLt) hJ_zero
  have hK_nofire := noFire_of_intervalFireCount_zero gc (right t)
    (Nat.le_of_lt ha_lt_s) (le_of_lt phase.s.isLt) hK_zero
  refine ⟨phase.s, phase.a, t, phase.hs_mover, phase.ha_nonmover, ?_, ?_, ?_⟩
  · exact (configVal_eq_of_noFire_between gc (left t) phase.a.val phase.s.val
      (Nat.le_of_lt ha_lt_s) phase.s.isLt hJ_nofire).symm
  · exact (configVal_eq_of_noFire_between gc t phase.a.val phase.s.val
      (Nat.le_of_lt ha_lt_s) phase.s.isLt phase.ht_nofire).symm
  · exact (configVal_eq_of_noFire_between gc (right t) phase.a.val phase.s.val
      (Nat.le_of_lt ha_lt_s) phase.s.isLt hK_nofire).symm

/-! ### Step 4: Full phase dispatch -/

/-- **Universal phase dispatch**: given a ternary phase and the existence of
    an entry conflict from ANY of the 3 proved mechanism conditions, derive
    hasEntryConflict.

    Case 1 (Both-Even): both J and K are even → bothEvenReturn_ec.
    Case 2 (Toggle-FR left): J ≥ 2, K = 0 → toggleFR_ec via consecutive
      fire pair of left(t) with right(t) silent.
    Case 3 (Toggle-FR right): J = 0, K ≥ 2 → toggleFR_ec_symm (symmetric).

    The Traversal Return cases (J=2,K=1) and (J=1,K=2) are absorbed into
    the upstream ring_alternation_forces_mechanism sorry: that sorry now
    only needs to produce a phase satisfying one of these 3 conditions.  -/
theorem phase_dispatch_ec (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hbL : sys.rs.m (left t) = 2)
    (hbR : sys.rs.m (right t) = 2)
    (hmech : let J := gc.intervalFireCount (left t) phase.a.val phase.s.val
             let K := gc.intervalFireCount (right t) phase.a.val phase.s.val
             (Even J ∧ Even K) ∨
             (J ≥ 2 ∧ K = 0) ∨
             (J = 0 ∧ K ≥ 2)) :
    hasEntryConflict gc := by
  simp only at hmech
  rcases hmech with hboth | hleft | hright
  · -- Both-Even Return
    exact phase_bothEven_ec gc t phase hbL hbR hboth.1 hboth.2
  · -- Toggle-FR left: J ≥ 2, K = 0
    -- left(t) fires ≥ 2 times, right(t) doesn't fire.
    -- Use minimum fire step to get ifc(a, k₁) = 0 then ifc(a, k₁+1) = 1.
    let fireSetL := (Finset.univ : Finset (Fin gc.configs.length)).filter
      (fun k => phase.a.val ≤ k.val ∧ k.val < phase.s.val ∧ gc.moverAt k = left t)
    have hneL : fireSetL.Nonempty := by
      obtain ⟨k, hka, hkb, hkm⟩ := exists_fire_step_in_interval gc (left t)
        (Nat.le_of_lt phase.ha_lt_s) (Nat.le_of_lt phase.s.isLt) (by omega)
      exact ⟨k, by simp [fireSetL]; exact ⟨hka, hkb, hkm⟩⟩
    obtain ⟨k₁, hk₁_mem, hk₁_min⟩ := Finset.exists_min_image fireSetL Fin.val hneL
    simp [fireSetL] at hk₁_mem
    obtain ⟨hk₁a, hk₁b, hk₁m⟩ := hk₁_mem
    have hnofire_bef : ∀ j : Fin gc.configs.length,
        phase.a.val ≤ j.val → j.val < k₁.val → gc.moverAt j ≠ left t := by
      intro j hja hjk hjm
      have hj_in : j ∈ fireSetL := by simp [fireSetL]; exact ⟨hja, by omega, hjm⟩
      have := hk₁_min j hj_in; omega
    have h_ifc0 : gc.intervalFireCount (left t) phase.a.val k₁.val = 0 :=
      intervalFireCount_eq_zero_of_noFire gc (left t) (by omega) (by omega) hnofire_bef
    have hone : gc.intervalFireCount (left t) k₁.val (k₁.val + 1) = 1 := by
      rw [intervalFireCount_single gc (left t) k₁.isLt]; simp [hk₁m]
    have hsplitK := intervalFireCount_split gc (left t) (show phase.a.val ≤ k₁.val by omega)
      (show k₁.val ≤ k₁.val + 1 by omega)
    have h_ifc1 : gc.intervalFireCount (left t) phase.a.val (k₁.val + 1) = 1 := by
      rw [hsplitK, h_ifc0, hone]
    have hsplit := intervalFireCount_split gc (left t)
      (show phase.a.val ≤ k₁.val + 1 by omega) (show k₁.val + 1 ≤ phase.s.val by omega)
    have hrest : gc.intervalFireCount (left t) (k₁.val + 1) phase.s.val ≥ 1 := by omega
    obtain ⟨k₂, hk₂a, hk₂b, hk₂m⟩ := exists_fire_step_in_interval gc (left t)
      (by omega) (Nat.le_of_lt phase.s.isLt) hrest
    -- Refine to consecutive pair
    obtain ⟨a', b', hk₁a', hb'k₂, hab', ha', hb', hno'⟩ :=
      exists_consecutive_fire_pair_bounded gc (left t) k₁ k₂ (by omega) hk₁m hk₂m
    -- Distinct values
    have hdiff := binary_distinct_at_consecutive_fires gc (left t) hbL a' b' hab' ha' hno'
    -- right(t) doesn't fire in [a, s) from K = 0
    have hR_nofire : ∀ k : Fin gc.configs.length,
        phase.a.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ right t :=
      noFire_of_intervalFireCount_zero gc (right t)
        (Nat.le_of_lt phase.ha_lt_s) (Nat.le_of_lt phase.s.isLt) hleft.2
    -- left(t) ≠ t (ring topology)
    have hlt_ne : left t ≠ t := by
      intro h; have := congrArg Fin.val h; simp only [left_val] at this
      have hn := sys.rs.n_ge_4; have ht := t.isLt
      by_cases h0 : t.val = 0
      · rw [h0] at this; simp at this; omega
      · rw [show t.val + sys.rs.n - 1 = (t.val - 1) + sys.rs.n from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at this; omega
    -- a' is not the mover of t (it fires left t)
    have ha'_nonmover : gc.moverAt a' ≠ t := by rw [ha']; exact hlt_ne
    have hb'_nonmover : gc.moverAt b' ≠ t := by rw [hb']; exact hlt_ne
    -- t doesn't fire in [a', s)
    have ht_nofire' : ∀ k : Fin gc.configs.length,
        a'.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ t := by
      intro k hk1 hk2
      -- a' ≥ k₁ ≥ phase.a, so k is in [phase.a, phase.s)
      exact phase.ht_nofire k (by omega) hk2
    -- right(t) doesn't fire in [a', s)
    have hR_nofire' : ∀ k : Fin gc.configs.length,
        a'.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ right t := by
      intro k hk1 hk2; exact hR_nofire k (by omega) hk2
    exact toggleFR_ec gc t a' b' phase.s hab' (by omega)
      phase.hs_mover ha'_nonmover hb'_nonmover ht_nofire'
      hbL hbR hR_nofire' hdiff
  · -- Toggle-FR right: J = 0, K ≥ 2 (symmetric)
    let fireSetR := (Finset.univ : Finset (Fin gc.configs.length)).filter
      (fun k => phase.a.val ≤ k.val ∧ k.val < phase.s.val ∧ gc.moverAt k = right t)
    have hneR : fireSetR.Nonempty := by
      obtain ⟨k, hka, hkb, hkm⟩ := exists_fire_step_in_interval gc (right t)
        (Nat.le_of_lt phase.ha_lt_s) (Nat.le_of_lt phase.s.isLt) (by omega)
      exact ⟨k, by simp [fireSetR]; exact ⟨hka, hkb, hkm⟩⟩
    obtain ⟨k₁, hk₁_mem, hk₁_min⟩ := Finset.exists_min_image fireSetR Fin.val hneR
    simp [fireSetR] at hk₁_mem
    obtain ⟨hk₁a, hk₁b, hk₁m⟩ := hk₁_mem
    have hnofire_bef : ∀ j : Fin gc.configs.length,
        phase.a.val ≤ j.val → j.val < k₁.val → gc.moverAt j ≠ right t := by
      intro j hja hjk hjm
      have hj_in : j ∈ fireSetR := by simp [fireSetR]; exact ⟨hja, by omega, hjm⟩
      have := hk₁_min j hj_in; omega
    have h_ifc0 : gc.intervalFireCount (right t) phase.a.val k₁.val = 0 :=
      intervalFireCount_eq_zero_of_noFire gc (right t) (by omega) (by omega) hnofire_bef
    have hone : gc.intervalFireCount (right t) k₁.val (k₁.val + 1) = 1 := by
      rw [intervalFireCount_single gc (right t) k₁.isLt]; simp [hk₁m]
    have hsplitK := intervalFireCount_split gc (right t) (show phase.a.val ≤ k₁.val by omega)
      (show k₁.val ≤ k₁.val + 1 by omega)
    have h_ifc1 : gc.intervalFireCount (right t) phase.a.val (k₁.val + 1) = 1 := by
      rw [hsplitK, h_ifc0, hone]
    have hsplit := intervalFireCount_split gc (right t)
      (show phase.a.val ≤ k₁.val + 1 by omega) (show k₁.val + 1 ≤ phase.s.val by omega)
    have hrest : gc.intervalFireCount (right t) (k₁.val + 1) phase.s.val ≥ 1 := by omega
    obtain ⟨k₂, hk₂a, hk₂b, hk₂m⟩ := exists_fire_step_in_interval gc (right t)
      (by omega) (Nat.le_of_lt phase.s.isLt) hrest
    obtain ⟨a', b', hk₁a', hb'k₂, hab', ha', hb', hno'⟩ :=
      exists_consecutive_fire_pair_bounded gc (right t) k₁ k₂ (by omega) hk₁m hk₂m
    have hdiff := binary_distinct_at_consecutive_fires gc (right t) hbR a' b' hab' ha' hno'
    have hL_nofire : ∀ k : Fin gc.configs.length,
        phase.a.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ left t :=
      noFire_of_intervalFireCount_zero gc (left t)
        (Nat.le_of_lt phase.ha_lt_s) (Nat.le_of_lt phase.s.isLt) hright.1
    have hrt_ne : right t ≠ t := by
      intro h; have := congrArg Fin.val h; simp only [right_val] at this
      have hn := sys.rs.n_ge_4; have ht := t.isLt
      by_cases hp1 : t.val + 1 < sys.rs.n
      · rw [Nat.mod_eq_of_lt hp1] at this; omega
      · rw [show t.val + 1 = sys.rs.n from by omega, Nat.mod_self] at this; omega
    have ha'_nonmover : gc.moverAt a' ≠ t := by rw [ha']; exact hrt_ne
    have hb'_nonmover : gc.moverAt b' ≠ t := by rw [hb']; exact hrt_ne
    have ht_nofire' : ∀ k : Fin gc.configs.length,
        a'.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ t :=
      fun k hk1 hk2 => phase.ht_nofire k (by omega) hk2
    have hL_nofire' : ∀ k : Fin gc.configs.length,
        a'.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ left t :=
      fun k hk1 hk2 => hL_nofire k (by omega) hk2
    exact toggleFR_ec_symm gc t a' b' phase.s hab' (by omega)
      phase.hs_mover ha'_nonmover hb'_nonmover ht_nofire'
      hbL hbR hL_nofire' hdiff

/-! ### Step 5: Pre-step neighbor lemma -/

/-- The step immediately before a mover step fires a neighbor or self.
    Since t doesn't fire in the gap, the pre-step fires left(t) or right(t). -/
private theorem pre_step_fires_neighbor
    (gc : GoodCycle sys)
    (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hgap : phase.s.val - phase.a.val ≥ 2) :
    gc.moverAt ⟨phase.s.val - 1,
        by have := phase.ha_lt_s; have := phase.s.isLt; omega⟩ = left t ∨
    gc.moverAt ⟨phase.s.val - 1,
        by have := phase.ha_lt_s; have := phase.s.isLt; omega⟩ = right t ∨
    gc.moverAt ⟨phase.s.val - 1,
        by have := phase.ha_lt_s; have := phase.s.isLt; omega⟩ = t := by
  have hs_lt := phase.s.isLt
  have ha_lt := phase.ha_lt_s
  set prev : Fin gc.configs.length := ⟨phase.s.val - 1, by omega⟩
  -- nextIndex prev = s (since s = prev + 1)
  have hnext : nextIndex gc.configs prev = phase.s := by
    ext; simp [nextIndex]
    show (phase.s.val - 1 + 1) % gc.configs.length = phase.s.val
    rw [show phase.s.val - 1 + 1 = phase.s.val from by omega]
    exact Nat.mod_eq_of_lt hs_lt
  -- next_mover_is_local: moverAt(s) ∈ {left(moverAt(prev)), moverAt(prev), right(moverAt(prev))}
  have hlocal := gc.next_mover_is_local prev
  simp only at hlocal
  rw [hnext, phase.hs_mover] at hlocal
  -- hlocal : t = left (moverAt prev) ∨ t = moverAt prev ∨ t = right (moverAt prev)
  -- We need: moverAt prev = left t ∨ moverAt prev = right t ∨ moverAt prev = t
  rcases hlocal with hleft | hself | hright
  · -- t = left (moverAt prev) → moverAt prev = right t
    right; left
    calc gc.moverAt prev
        = right (left (gc.moverAt prev)) := (right_left_eq_self _).symm
      _ = right t := by rw [hleft]
  · -- t = moverAt prev
    right; right; exact hself.symm
  · -- t = right (moverAt prev) → moverAt prev = left t
    left
    calc gc.moverAt prev
        = left (right (gc.moverAt prev)) := (left_right_eq_self _).symm
      _ = left t := by rw [hright]

/-! ### Step 5b: Per-gap normal form classification -/

/-- A gap of ternary t is "mechanism-triggering" if its (J, K) interval
    fire counts satisfy BothEven, ToggleFR-left, or ToggleFR-right. -/
def isMechanismTriggering (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t) : Prop :=
  let J := gc.intervalFireCount (left t) phase.a.val phase.s.val
  let K := gc.intervalFireCount (right t) phase.a.val phase.s.val
  (Even J ∧ Even K) ∨ (J ≥ 2 ∧ K = 0) ∨ (J = 0 ∧ K ≥ 2)

/-- A gap is in "normal form" if it is NOT mechanism-triggering.
    In this case, per the counting argument (Stage A), the gap must have
    (J, K) ∈ {(1,0), (0,1), (1,1), or mixed odd/even with both nonzero}.

    The stronger constraint (exactly (1,0), (0,1), (1,1)) follows from
    the GLOBAL counting argument over all gaps simultaneously. -/
def isNormalFormGap (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t) : Prop :=
  ¬isMechanismTriggering gc t phase

/-- Per-gap constraint: if a gap is not mechanism-triggering, then:
    - If J = 0, then K = 1 (not K ≥ 2 by ToggleFR-right, not K = 0 by BothEven (0,0))
    - If K = 0, then J = 1 (symmetric)
    - If both > 0, at least one is odd (not both even by BothEven) -/
theorem normalForm_gap_constraint (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hnorm : isNormalFormGap gc t phase) :
    let J := gc.intervalFireCount (left t) phase.a.val phase.s.val
    let K := gc.intervalFireCount (right t) phase.a.val phase.s.val
    (J = 0 → K = 1) ∧ (K = 0 → J = 1) ∧ (J > 0 → K > 0 → ¬(Even J ∧ Even K)) := by
  simp only
  set J := gc.intervalFireCount (left t) phase.a.val phase.s.val
  set K := gc.intervalFireCount (right t) phase.a.val phase.s.val
  -- hnorm : ¬isMechanismTriggering gc t phase, which unfolds to
  -- ¬((Even J ∧ Even K) ∨ (J ≥ 2 ∧ K = 0) ∨ (J = 0 ∧ K ≥ 2))
  have h_not_bothEven : ¬(Even J ∧ Even K) := fun h => hnorm (Or.inl h)
  have h_not_toggleL : ¬(J ≥ 2 ∧ K = 0) := fun h => hnorm (Or.inr (Or.inl h))
  have h_not_toggleR : ¬(J = 0 ∧ K ≥ 2) := fun h => hnorm (Or.inr (Or.inr h))
  refine ⟨fun hJ0 => ?_, fun hK0 => ?_, fun _ _ hboth => ?_⟩
  · -- J = 0 → K = 1
    -- From h_not_toggleR: ¬(J = 0 ∧ K ≥ 2) with J = 0 → K < 2
    have hK_lt_2 : K < 2 := by
      by_contra hge2; push_neg at hge2
      exact h_not_toggleR ⟨hJ0, hge2⟩
    -- From h_not_bothEven: J=0 is even → K is not even → K is odd
    have hK_odd : ¬Even K := by
      intro hKeven
      exact h_not_bothEven ⟨⟨0, by omega⟩, hKeven⟩
    -- K < 2 and K is odd → K = 1
    interval_cases K <;> simp_all
  · -- K = 0 → J = 1 (symmetric)
    have hJ_lt_2 : J < 2 := by
      by_contra hge2; push_neg at hge2
      exact h_not_toggleL ⟨hge2, hK0⟩
    have hJ_odd : ¬Even J := by
      intro hJeven
      exact h_not_bothEven ⟨hJeven, ⟨0, by omega⟩⟩
    interval_cases J <;> simp_all
  · -- Both > 0 → not both even (directly from h_not_bothEven)
    exact h_not_bothEven hboth

/-- A normal phase of length 1 must start with a binary-neighbor fire. -/
theorem normal_len1_phase_starts_at_neighbor
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hnorm : isNormalFormGap gc t phase)
    (hlen1 : phase.s.val = phase.a.val + 1) :
    gc.moverAt phase.a = left t ∨ gc.moverAt phase.a = right t := by
  set J := gc.intervalFireCount (left t) phase.a.val phase.s.val with hJ
  set K := gc.intervalFireCount (right t) phase.a.val phase.s.val with hK
  have hconstraint := normalForm_gap_constraint gc t phase hnorm
  by_cases hL : gc.moverAt phase.a = left t
  · exact Or.inl hL
  · by_cases hR : gc.moverAt phase.a = right t
    · exact Or.inr hR
    · have hJ0 : J = 0 := by
        rw [hJ, hlen1, intervalFireCount_single gc (left t) phase.a.isLt]
        simp [hL]
      have hK0 : K = 0 := by
        rw [hK, hlen1, intervalFireCount_single gc (right t) phase.a.isLt]
        simp [hR]
      have : K = 1 := hconstraint.1 hJ0
      omega

/-- In a one-sided normal phase with `K = 0`, the step immediately before the
    `t`-fire must be the unique `left t` fire. -/
private theorem one_sided_normal_prev_left
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hnorm : isNormalFormGap gc t phase)
    (hJ1 : gc.intervalFireCount (left t) phase.a.val phase.s.val = 1)
    (hK0 : gc.intervalFireCount (right t) phase.a.val phase.s.val = 0)
    (hgap2 : phase.s.val - phase.a.val ≥ 2) :
    gc.moverAt ⟨phase.s.val - 1,
        by have := phase.ha_lt_s; have := phase.s.isLt; omega⟩ = left t := by
  set prev : Fin gc.configs.length := ⟨phase.s.val - 1, by
    have := phase.ha_lt_s
    have := phase.s.isLt
    omega⟩
  have hprev_ge_a : phase.a.val ≤ prev.val := by
    dsimp [prev]
    omega
  have hprev_lt_s : prev.val < phase.s.val := by
    dsimp [prev]
    omega
  have hright_ne : gc.moverAt prev ≠ right t := by
    exact noFire_of_intervalFireCount_zero gc (right t)
      (show phase.a.val ≤ phase.s.val by omega)
      (Nat.le_of_lt phase.s.isLt) hK0 prev hprev_ge_a hprev_lt_s
  rcases pre_step_fires_neighbor gc t phase hgap2 with hprevL | hprevR | hprevT
  · exact hprevL
  · exact False.elim (hright_ne hprevR)
  · exact False.elim (phase.ht_nofire prev hprev_ge_a hprev_lt_s hprevT)

/-- Symmetric one-sided normal phase lemma. -/
private theorem one_sided_normal_prev_right
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hnorm : isNormalFormGap gc t phase)
    (hJ0 : gc.intervalFireCount (left t) phase.a.val phase.s.val = 0)
    (hK1 : gc.intervalFireCount (right t) phase.a.val phase.s.val = 1)
    (hgap2 : phase.s.val - phase.a.val ≥ 2) :
    gc.moverAt ⟨phase.s.val - 1,
        by have := phase.ha_lt_s; have := phase.s.isLt; omega⟩ = right t := by
  set prev : Fin gc.configs.length := ⟨phase.s.val - 1, by
    have := phase.ha_lt_s
    have := phase.s.isLt
    omega⟩
  have hprev_ge_a : phase.a.val ≤ prev.val := by
    dsimp [prev]
    omega
  have hprev_lt_s : prev.val < phase.s.val := by
    dsimp [prev]
    omega
  have hleft_ne : gc.moverAt prev ≠ left t := by
    exact noFire_of_intervalFireCount_zero gc (left t)
      (show phase.a.val ≤ phase.s.val by omega)
      (Nat.le_of_lt phase.s.isLt) hJ0 prev hprev_ge_a hprev_lt_s
  rcases pre_step_fires_neighbor gc t phase hgap2 with hprevL | hprevR | hprevT
  · exact False.elim (hleft_ne hprevL)
  · exact hprevR
  · exact False.elim (phase.ht_nofire prev hprev_ge_a hprev_lt_s hprevT)

/-- Suffix-normal specialization: if a suffix phase has no right-neighbor
    fires, then it has exactly one left-neighbor fire. -/
private theorem suffix_normal_zero_right_one_left
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall_normal : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t)
    (a' : Fin gc.configs.length)
    (ha' : phase.a.val ≤ a'.val)
    (ha'_lt_s : a'.val < phase.s.val)
    (ha'_nonmover : gc.moverAt a' ≠ t)
    (hK_zero : gc.intervalFireCount (right t) a'.val phase.s.val = 0) :
    gc.intervalFireCount (left t) a'.val phase.s.val = 1 := by
  let phase' := phase.suffix a' ha' ha'_lt_s ha'_nonmover
  have hnorm' : isNormalFormGap gc t phase' := hall_normal phase'
  have hconstraint := normalForm_gap_constraint gc t phase' hnorm'
  exact hconstraint.2.1 hK_zero

/-- Symmetric suffix-normal specialization: if a suffix phase has no left-neighbor
    fires, then it has exactly one right-neighbor fire. -/
private theorem suffix_normal_zero_left_one_right
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall_normal : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t)
    (a' : Fin gc.configs.length)
    (ha' : phase.a.val ≤ a'.val)
    (ha'_lt_s : a'.val < phase.s.val)
    (ha'_nonmover : gc.moverAt a' ≠ t)
    (hJ_zero : gc.intervalFireCount (left t) a'.val phase.s.val = 0) :
    gc.intervalFireCount (right t) a'.val phase.s.val = 1 := by
  let phase' := phase.suffix a' ha' ha'_lt_s ha'_nonmover
  have hnorm' : isNormalFormGap gc t phase' := hall_normal phase'
  have hconstraint := normalForm_gap_constraint gc t phase' hnorm'
  exact hconstraint.1 hJ_zero

/-- In a mixed normal phase (both binary neighbors fire at least once),
    looking after the later of the two last-neighbor fires produces a shorter
    one-sided normal suffix. -/
private theorem mixed_normal_has_one_sided_suffix
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall_normal : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t)
    (hJ_pos : 0 < gc.intervalFireCount (left t) phase.a.val phase.s.val)
    (hK_pos : 0 < gc.intervalFireCount (right t) phase.a.val phase.s.val) :
    ∃ a' : Fin gc.configs.length,
      phase.a.val < a'.val ∧
      a'.val < phase.s.val ∧
      gc.moverAt a' ≠ t ∧
      ((gc.intervalFireCount (left t) a'.val phase.s.val = 1 ∧
        gc.intervalFireCount (right t) a'.val phase.s.val = 0) ∨
       (gc.intervalFireCount (left t) a'.val phase.s.val = 0 ∧
        gc.intervalFireCount (right t) a'.val phase.s.val = 1)) := by
  obtain ⟨kL, hkLa, hkLb, hkLm⟩ := exists_fire_step_in_interval gc (left t)
    (Nat.le_of_lt phase.ha_lt_s) (Nat.le_of_lt phase.s.isLt) (by omega)
  obtain ⟨kR, hkRa, hkRb, hkRm⟩ := exists_fire_step_in_interval gc (right t)
    (Nat.le_of_lt phase.ha_lt_s) (Nat.le_of_lt phase.s.isLt) (by omega)
  let fireSetL := (Finset.univ : Finset (Fin gc.configs.length)).filter
    (fun k => phase.a.val ≤ k.val ∧ k.val < phase.s.val ∧ gc.moverAt k = left t)
  let fireSetR := (Finset.univ : Finset (Fin gc.configs.length)).filter
    (fun k => phase.a.val ≤ k.val ∧ k.val < phase.s.val ∧ gc.moverAt k = right t)
  have hneL : fireSetL.Nonempty := by
    exact ⟨kL, by simp [fireSetL]; exact ⟨hkLa, hkLb, hkLm⟩⟩
  have hneR : fireSetR.Nonempty := by
    exact ⟨kR, by simp [fireSetR]; exact ⟨hkRa, hkRb, hkRm⟩⟩
  obtain ⟨l_last, hl_mem, hl_max⟩ := Finset.exists_max_image fireSetL Fin.val hneL
  obtain ⟨r_last, hr_mem, hr_max⟩ := Finset.exists_max_image fireSetR Fin.val hneR
  simp [fireSetL] at hl_mem
  simp [fireSetR] at hr_mem
  obtain ⟨hl_a, hl_b, hl_m⟩ := hl_mem
  obtain ⟨hr_a, hr_b, hr_m⟩ := hr_mem
  have hno_left_after : ∀ j : Fin gc.configs.length,
      l_last.val < j.val → j.val < phase.s.val → gc.moverAt j ≠ left t := by
    intro j hj1 hj2 hjm
    have : j ∈ fireSetL := by simp [fireSetL]; exact ⟨by omega, hj2, hjm⟩
    have := hl_max j this
    omega
  have hno_right_after : ∀ j : Fin gc.configs.length,
      r_last.val < j.val → j.val < phase.s.val → gc.moverAt j ≠ right t := by
    intro j hj1 hj2 hjm
    have : j ∈ fireSetR := by simp [fireSetR]; exact ⟨by omega, hj2, hjm⟩
    have := hr_max j this
    omega
  by_cases horder : l_last.val < r_last.val
  · have ha'_lt_s : l_last.val + 1 < phase.s.val := by omega
    have ha'_lt_len : l_last.val + 1 < gc.configs.length := by
      exact lt_trans ha'_lt_s phase.s.isLt
    let a' : Fin gc.configs.length := ⟨l_last.val + 1, ha'_lt_len⟩
    have ha'_gt_a : phase.a.val < a'.val := by
      exact by
        dsimp [a']
        omega
    have ha'_lt_s' : a'.val < phase.s.val := by
      exact by
        dsimp [a']
        exact ha'_lt_s
    have ha'_nonmover : gc.moverAt a' ≠ t := by
      exact phase.ht_nofire a' (Nat.le_of_lt ha'_gt_a) ha'_lt_s'
    have hleft_zero : gc.intervalFireCount (left t) a'.val phase.s.val = 0 := by
      exact intervalFireCount_eq_zero_of_noFire gc (left t)
        (Nat.le_of_lt ha'_lt_s') (Nat.le_of_lt phase.s.isLt)
        (fun j hj1 hj2 => hno_left_after j (by
          dsimp [a'] at hj1
          omega) hj2)
    refine ⟨a', ha'_gt_a, ha'_lt_s', ha'_nonmover, Or.inr ?_⟩
    · constructor
      · exact hleft_zero
      · exact suffix_normal_zero_left_one_right gc t hall_normal phase
          a' (Nat.le_of_lt ha'_gt_a) ha'_lt_s'
          ha'_nonmover hleft_zero
  · have hrle : r_last.val ≤ l_last.val := by omega
    have hstrict : r_last.val < l_last.val := by
      by_contra hEq
      have hrev : l_last.val ≤ r_last.val := by omega
      have hEqVal : l_last.val = r_last.val := by omega
      have hEqFin : l_last = r_last := Fin.ext hEqVal
      rw [← hEqFin] at hr_m
      have : left t = right t := hl_m.symm.trans hr_m
      have hrr_eq : t = right (right t) := by
        have hright := congrArg right this
        simpa [right_left_eq_self] using hright
      have hrr_ne : right (right t) ≠ t := by
        intro hrr
        have hval := congrArg Fin.val hrr
        simp only [right_val] at hval
        have ht := t.isLt
        have hn4 := sys.rs.n_ge_4
        by_cases hnext : t.val + 1 < sys.rs.n
        · rw [Nat.mod_eq_of_lt hnext] at hval
          by_cases hnext2 : t.val + 1 + 1 < sys.rs.n
          · rw [Nat.mod_eq_of_lt hnext2] at hval
            omega
          · rw [show t.val + 1 + 1 = sys.rs.n from by omega, Nat.mod_self] at hval
            omega
        · rw [show t.val + 1 = sys.rs.n from by omega, Nat.mod_self,
            Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < sys.rs.n)] at hval
          omega
      exact hrr_ne hrr_eq.symm
    have ha'_lt_s : r_last.val + 1 < phase.s.val := by omega
    have ha'_lt_len : r_last.val + 1 < gc.configs.length := by
      exact lt_trans ha'_lt_s phase.s.isLt
    let a' : Fin gc.configs.length := ⟨r_last.val + 1, ha'_lt_len⟩
    have ha'_gt_a : phase.a.val < a'.val := by
      exact by
        dsimp [a']
        omega
    have ha'_lt_s' : a'.val < phase.s.val := by
      exact by
        dsimp [a']
        exact ha'_lt_s
    have ha'_nonmover : gc.moverAt a' ≠ t := by
      exact phase.ht_nofire a' (Nat.le_of_lt ha'_gt_a) ha'_lt_s'
    have hright_zero : gc.intervalFireCount (right t) a'.val phase.s.val = 0 := by
      exact intervalFireCount_eq_zero_of_noFire gc (right t)
        (Nat.le_of_lt ha'_lt_s') (Nat.le_of_lt phase.s.isLt)
        (fun j hj1 hj2 => hno_right_after j (by
          dsimp [a'] at hj1
          omega) hj2)
    refine ⟨a', ha'_gt_a, ha'_lt_s', ha'_nonmover, Or.inl ?_⟩
    · constructor
      · exact suffix_normal_zero_right_one_left gc t hall_normal phase
          a' (Nat.le_of_lt ha'_gt_a) ha'_lt_s'
          ha'_nonmover hright_zero
      · exact hright_zero

/-- A length-2 tail `x, left(t), t` gives an immediate entry conflict at
    `left t` as soon as the first mover `x` is outside the local
    `{left(left t), left t, t}` neighborhood of `left t`.

    This is the one-step context-preservation pattern: between step `a`
    and step `a+1`, only the mover at step `a` can change any value. If
    that mover is not in the 3-neighborhood of `left t`, then the local
    context at `left t` is identical at the non-mover step `a` and the
    mover step `a+1`. -/
private theorem len2_left_tail_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hlen2 : phase.s.val = phase.a.val + 2)
    (ha1_left : gc.moverAt ⟨phase.a.val + 1, by
      have := phase.s.isLt
      omega⟩ = left t)
    (ha_ne_ll : gc.moverAt phase.a ≠ left (left t))
    (ha_ne_l : gc.moverAt phase.a ≠ left t)
    (ha_ne_t : gc.moverAt phase.a ≠ t) :
    hasEntryConflict gc := by
  have ha1_lt : phase.a.val + 1 < gc.configs.length := by
    have := phase.s.isLt
    omega
  set a1 : Fin gc.configs.length := ⟨phase.a.val + 1, by
    have := phase.s.isLt
    omega⟩
  have ha1_eq_next : a1 = nextIndex gc.configs phase.a := by
    apply Fin.ext
    simp [a1, nextIndex]
    rw [Nat.mod_eq_of_lt ha1_lt]
  refine ⟨a1, phase.a, left t, ha1_left, ha_ne_l, ?_, ?_, ?_⟩
  · -- left(left t) unchanged across step a
    rw [ha1_eq_next]
    exact gc.state_eq_of_ne_moverAt phase.a (left (left t)) ha_ne_ll.symm
  · -- left(t) unchanged across step a
    rw [ha1_eq_next]
    exact gc.state_eq_of_ne_moverAt phase.a (left t) ha_ne_l.symm
  · -- t unchanged across step a
    rw [ha1_eq_next]
    rw [right_left_eq_self]
    exact gc.state_eq_of_ne_moverAt phase.a t ha_ne_t.symm

/-- Symmetric length-2 tail lemma for `x, right(t), t`. -/
private theorem len2_right_tail_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hlen2 : phase.s.val = phase.a.val + 2)
    (ha1_right : gc.moverAt ⟨phase.a.val + 1, by
      have := phase.s.isLt
      omega⟩ = right t)
    (ha_ne_t : gc.moverAt phase.a ≠ t)
    (ha_ne_r : gc.moverAt phase.a ≠ right t)
    (ha_ne_rr : gc.moverAt phase.a ≠ right (right t)) :
    hasEntryConflict gc := by
  have ha1_lt : phase.a.val + 1 < gc.configs.length := by
    have := phase.s.isLt
    omega
  set a1 : Fin gc.configs.length := ⟨phase.a.val + 1, by
    have := phase.s.isLt
    omega⟩
  have ha1_eq_next : a1 = nextIndex gc.configs phase.a := by
    apply Fin.ext
    simp [a1, nextIndex]
    rw [Nat.mod_eq_of_lt ha1_lt]
  refine ⟨a1, phase.a, right t, ha1_right, ha_ne_r, ?_, ?_, ?_⟩
  · -- t unchanged across step a
    rw [ha1_eq_next]
    rw [left_right_eq_self]
    exact gc.state_eq_of_ne_moverAt phase.a t ha_ne_t.symm
  · -- right(t) unchanged across step a
    rw [ha1_eq_next]
    exact gc.state_eq_of_ne_moverAt phase.a (right t) ha_ne_r.symm
  · -- right(right t) unchanged across step a
    rw [ha1_eq_next]
    exact gc.state_eq_of_ne_moverAt phase.a (right (right t)) ha_ne_rr.symm

/-- Any length-2 phase is already tightly localized: either its first mover lies
    in the 5-neighborhood `{left(left t), left t, right t, right(right t)}`
    of the pivot `t`, or the phase yields an immediate entry conflict via one of
    the two length-2 tail lemmas above. -/
private theorem len2_phase_start_in_five_or_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hlen2 : phase.s.val = phase.a.val + 2) :
    hasEntryConflict gc ∨
    gc.moverAt phase.a = left (left t) ∨
    gc.moverAt phase.a = left t ∨
    gc.moverAt phase.a = right t ∨
    gc.moverAt phase.a = right (right t) := by
  have hgap2 : phase.s.val - phase.a.val ≥ 2 := by omega
  let prev : Fin gc.configs.length := ⟨phase.s.val - 1, by
    have := phase.ha_lt_s
    have := phase.s.isLt
    omega⟩
  let a1 : Fin gc.configs.length := ⟨phase.a.val + 1, by
    have := phase.s.isLt
    omega⟩
  have hprev_eq_a1 : prev = a1 := by
    apply Fin.ext
    dsimp [prev, a1]
    omega
  have hprev_not_t : gc.moverAt prev ≠ t := by
    exact phase.ht_nofire prev (by
      dsimp [prev]
      omega) (by
      dsimp [prev]
      omega)
  rcases pre_step_fires_neighbor gc t phase hgap2 with hprev_left | hprev_right | hprev_t
  · have ha1_left : gc.moverAt a1 = left t := by
      rw [← hprev_eq_a1]
      exact hprev_left
    by_cases ha_ll : gc.moverAt phase.a = left (left t)
    · exact Or.inr (Or.inl ha_ll)
    · by_cases ha_l : gc.moverAt phase.a = left t
      · exact Or.inr (Or.inr (Or.inl ha_l))
      · exact Or.inl (len2_left_tail_ec gc t phase hlen2 ha1_left ha_ll ha_l phase.ha_nonmover)
  · have ha1_right : gc.moverAt a1 = right t := by
      rw [← hprev_eq_a1]
      exact hprev_right
    by_cases ha_r : gc.moverAt phase.a = right t
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha_r)))
    · by_cases ha_rr : gc.moverAt phase.a = right (right t)
      · exact Or.inr (Or.inr (Or.inr (Or.inr ha_rr)))
      · exact Or.inl (len2_right_tail_ec gc t phase hlen2 ha1_right phase.ha_nonmover ha_r ha_rr)
  · exact False.elim (hprev_not_t hprev_t)

/-- In a one-sided normal length-2 phase with unique left-neighbor fire,
    the first mover must be `left (left t)` unless the phase already yields
    an entry conflict. -/
theorem one_sided_left_len2_start_ll_or_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hnorm : isNormalFormGap gc t phase)
    (hJ1 : gc.intervalFireCount (left t) phase.a.val phase.s.val = 1)
    (hK0 : gc.intervalFireCount (right t) phase.a.val phase.s.val = 0)
    (hlen2 : phase.s.val = phase.a.val + 2) :
    hasEntryConflict gc ∨ gc.moverAt phase.a = left (left t) := by
  have hgap2 : phase.s.val - phase.a.val ≥ 2 := by omega
  have hprev_left := one_sided_normal_prev_left gc t phase hnorm hJ1 hK0 hgap2
  let a1 : Fin gc.configs.length := ⟨phase.a.val + 1, by
    have := phase.s.isLt
    omega⟩
  have ha1_eq_prev : a1 = ⟨phase.s.val - 1, by
      have := phase.ha_lt_s
      have := phase.s.isLt
      omega⟩ := by
    apply Fin.ext
    dsimp [a1]
    omega
  have ha1_left : gc.moverAt a1 = left t := by
    rw [ha1_eq_prev]
    exact hprev_left
  by_cases ha_ll : gc.moverAt phase.a = left (left t)
  · exact Or.inr ha_ll
  · by_cases ha_l : gc.moverAt phase.a = left t
    · have hJ2 : gc.intervalFireCount (left t) phase.a.val phase.s.val = 2 := by
        rw [hlen2]
        rw [intervalFireCount_split gc (left t) (a := phase.a.val) (c := phase.a.val + 1) (b := phase.a.val + 2)]
        · have hone2 : gc.intervalFireCount (left t) (phase.a.val + 1) (phase.a.val + 2) = 1 := by
            rw [intervalFireCount_single gc (left t) (by
              have := phase.s.isLt
              omega)]
            have hmk : gc.moverAt ⟨phase.a.val + 1, by
                have := phase.s.isLt
                omega⟩ = left t := by
              simpa [a1] using ha1_left
            simp [hmk]
          rw [intervalFireCount_single gc (left t) phase.a.isLt, hone2]
          simp [ha_l]
        · omega
        · omega
      omega
    · exact Or.inl (len2_left_tail_ec gc t phase hlen2 ha1_left ha_ll ha_l phase.ha_nonmover)

/-- Symmetric one-sided length-2 reduction. -/
theorem one_sided_right_len2_start_rr_or_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hnorm : isNormalFormGap gc t phase)
    (hJ0 : gc.intervalFireCount (left t) phase.a.val phase.s.val = 0)
    (hK1 : gc.intervalFireCount (right t) phase.a.val phase.s.val = 1)
    (hlen2 : phase.s.val = phase.a.val + 2) :
    hasEntryConflict gc ∨ gc.moverAt phase.a = right (right t) := by
  have hgap2 : phase.s.val - phase.a.val ≥ 2 := by omega
  have hprev_right := one_sided_normal_prev_right gc t phase hnorm hJ0 hK1 hgap2
  let a1 : Fin gc.configs.length := ⟨phase.a.val + 1, by
    have := phase.s.isLt
    omega⟩
  have ha1_eq_prev : a1 = ⟨phase.s.val - 1, by
      have := phase.ha_lt_s
      have := phase.s.isLt
      omega⟩ := by
    apply Fin.ext
    dsimp [a1]
    omega
  have ha1_right : gc.moverAt a1 = right t := by
    rw [ha1_eq_prev]
    exact hprev_right
  by_cases ha_rr : gc.moverAt phase.a = right (right t)
  · exact Or.inr ha_rr
  · by_cases ha_r : gc.moverAt phase.a = right t
    · have hK2 : gc.intervalFireCount (right t) phase.a.val phase.s.val = 2 := by
        rw [hlen2]
        rw [intervalFireCount_split gc (right t) (a := phase.a.val) (c := phase.a.val + 1) (b := phase.a.val + 2)]
        · have hone2 : gc.intervalFireCount (right t) (phase.a.val + 1) (phase.a.val + 2) = 1 := by
            rw [intervalFireCount_single gc (right t) (by
              have := phase.s.isLt
              omega)]
            have hmk : gc.moverAt ⟨phase.a.val + 1, by
                have := phase.s.isLt
                omega⟩ = right t := by
              simpa [a1] using ha1_right
            simp [hmk]
          rw [intervalFireCount_single gc (right t) phase.a.isLt, hone2]
          simp [ha_r]
        · omega
        · omega
      omega
    · exact Or.inl (len2_right_tail_ec gc t phase hlen2 ha1_right phase.ha_nonmover ha_r ha_rr)

private theorem normal_phase_has_len1_suffix
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall_normal : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t) :
    ∃ phase1 : TernaryPhase gc t,
      phase1.s = phase.s ∧
      phase1.s.val = phase1.a.val + 1 ∧
      isNormalFormGap gc t phase1 ∧
      (gc.moverAt phase1.a = left t ∨ gc.moverAt phase1.a = right t) := by
  let hnorm := hall_normal phase
  by_cases hlen1 : phase.s.val = phase.a.val + 1
  · refine ⟨phase, rfl, hlen1, hnorm, ?_⟩
    exact normal_len1_phase_starts_at_neighbor gc t phase hnorm hlen1
  · have hgap2 : phase.s.val - phase.a.val ≥ 2 := by
      have hsucc_le : phase.a.val + 1 ≤ phase.s.val := Nat.succ_le_of_lt phase.ha_lt_s
      have hstrict : phase.a.val + 1 < phase.s.val := by
        apply Nat.lt_of_le_of_ne hsucc_le
        simpa [eq_comm] using hlen1
      omega
    set J := gc.intervalFireCount (left t) phase.a.val phase.s.val
    set K := gc.intervalFireCount (right t) phase.a.val phase.s.val
    by_cases hJ0 : J = 0
    · have hK1 : K = 1 := (normalForm_gap_constraint gc t phase hnorm).1 hJ0
      let prev : Fin gc.configs.length := ⟨phase.s.val - 1, by
        have := phase.ha_lt_s
        have := phase.s.isLt
        omega⟩
      have hprev_ge_a : phase.a.val ≤ prev.val := by
        dsimp [prev]
        omega
      have hprev_lt_s : prev.val < phase.s.val := by
        dsimp [prev]
        omega
      have hprev_nonmover : gc.moverAt prev ≠ t := phase.ht_nofire prev hprev_ge_a hprev_lt_s
      let phase1 := phase.suffix prev hprev_ge_a hprev_lt_s hprev_nonmover
      have hnorm1 : isNormalFormGap gc t phase1 := hall_normal phase1
      have hprev_right : gc.moverAt prev = right t := by
        simpa [J, K] using one_sided_normal_prev_right gc t phase hnorm hJ0 hK1 hgap2
      refine ⟨phase1, rfl, ?_, hnorm1, Or.inr ?_⟩
      · dsimp [phase1, TernaryPhase.suffix, prev]
        omega
      · simpa [phase1, TernaryPhase.suffix, prev] using hprev_right
    · by_cases hK0 : K = 0
      · have hJ1 : J = 1 := (normalForm_gap_constraint gc t phase hnorm).2.1 hK0
        let prev : Fin gc.configs.length := ⟨phase.s.val - 1, by
          have := phase.ha_lt_s
          have := phase.s.isLt
          omega⟩
        have hprev_ge_a : phase.a.val ≤ prev.val := by
          dsimp [prev]
          omega
        have hprev_lt_s : prev.val < phase.s.val := by
          dsimp [prev]
          omega
        have hprev_nonmover : gc.moverAt prev ≠ t := phase.ht_nofire prev hprev_ge_a hprev_lt_s
        let phase1 := phase.suffix prev hprev_ge_a hprev_lt_s hprev_nonmover
        have hnorm1 : isNormalFormGap gc t phase1 := hall_normal phase1
        have hprev_left : gc.moverAt prev = left t := by
          simpa [J, K] using one_sided_normal_prev_left gc t phase hnorm hJ1 hK0 hgap2
        refine ⟨phase1, rfl, ?_, hnorm1, Or.inl ?_⟩
        · dsimp [phase1, TernaryPhase.suffix, prev]
          omega
        · simpa [phase1, TernaryPhase.suffix, prev] using hprev_left
      · have hJ_pos : 0 < J := by
          have : J ≠ 0 := hJ0
          omega
        have hK_pos : 0 < K := by
          have : K ≠ 0 := hK0
          omega
        obtain ⟨a', ha'_gt_a, ha'_lt_s, ha'_nonmover, hsuffix⟩ :=
          mixed_normal_has_one_sided_suffix gc t hall_normal phase hJ_pos hK_pos
        let phase' := phase.suffix a' (Nat.le_of_lt ha'_gt_a) ha'_lt_s ha'_nonmover
        have hnorm' : isNormalFormGap gc t phase' := hall_normal phase'
        by_cases hlen1' : phase'.s.val = phase'.a.val + 1
        · refine ⟨phase', rfl, hlen1', hnorm', ?_⟩
          exact normal_len1_phase_starts_at_neighbor gc t phase' hnorm' hlen1'
        · have hgap2' : phase'.s.val - phase'.a.val ≥ 2 := by
            have hsucc_le' : phase'.a.val + 1 ≤ phase'.s.val := Nat.succ_le_of_lt phase'.ha_lt_s
            have hstrict' : phase'.a.val + 1 < phase'.s.val := by
              apply Nat.lt_of_le_of_ne hsucc_le'
              simpa [eq_comm] using hlen1'
            omega
          rcases hsuffix with ⟨hJ1', hK0'⟩ | ⟨hJ0', hK1'⟩
          · let prev : Fin gc.configs.length := ⟨phase'.s.val - 1, by
              have := phase'.ha_lt_s
              have := phase'.s.isLt
              omega⟩
            have hprev_ge_a : phase'.a.val ≤ prev.val := by
              dsimp [prev]
              omega
            have hprev_lt_s : prev.val < phase'.s.val := by
              dsimp [prev]
              omega
            have hprev_nonmover : gc.moverAt prev ≠ t :=
              phase'.ht_nofire prev hprev_ge_a hprev_lt_s
            let phase1 := phase'.suffix prev hprev_ge_a hprev_lt_s hprev_nonmover
            have hnorm1 : isNormalFormGap gc t phase1 := hall_normal phase1
            have hprev_left : gc.moverAt prev = left t := by
              simpa using one_sided_normal_prev_left gc t phase' hnorm' hJ1' hK0' hgap2'
            refine ⟨phase1, by rfl, ?_, hnorm1, Or.inl ?_⟩
            · dsimp [phase1, phase', TernaryPhase.suffix, prev]
              omega
            · simpa [phase1, phase', TernaryPhase.suffix, prev] using hprev_left
          · let prev : Fin gc.configs.length := ⟨phase'.s.val - 1, by
              have := phase'.ha_lt_s
              have := phase'.s.isLt
              omega⟩
            have hprev_ge_a : phase'.a.val ≤ prev.val := by
              dsimp [prev]
              omega
            have hprev_lt_s : prev.val < phase'.s.val := by
              dsimp [prev]
              omega
            have hprev_nonmover : gc.moverAt prev ≠ t :=
              phase'.ht_nofire prev hprev_ge_a hprev_lt_s
            let phase1 := phase'.suffix prev hprev_ge_a hprev_lt_s hprev_nonmover
            have hnorm1 : isNormalFormGap gc t phase1 := hall_normal phase1
            have hprev_right : gc.moverAt prev = right t := by
              simpa using one_sided_normal_prev_right gc t phase' hnorm' hJ0' hK1' hgap2'
            refine ⟨phase1, by rfl, ?_, hnorm1, Or.inr ?_⟩
            · dsimp [phase1, phase', TernaryPhase.suffix, prev]
              omega
            · simpa [phase1, phase', TernaryPhase.suffix, prev] using hprev_right

private theorem normal_phase_len_le2_localized_or_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hnorm : isNormalFormGap gc t phase)
    (hlen_le2 : phase.s.val ≤ phase.a.val + 2) :
    hasEntryConflict gc ∨
    ∀ k : Fin gc.configs.length,
      phase.a.val ≤ k.val → k.val < phase.s.val →
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) := by
  by_cases hlen1 : phase.s.val = phase.a.val + 1
  · right
    intro k hk1 hk2
    have hk_eq : k = phase.a := by
      apply Fin.ext
      omega
    rcases normal_len1_phase_starts_at_neighbor gc t phase hnorm hlen1 with hk | hk
    · right; left
      simpa [hk_eq] using hk
    · right; right; left
      simpa [hk_eq] using hk
  · have hlen2 : phase.s.val = phase.a.val + 2 := by
      have hsucc_le : phase.a.val + 1 ≤ phase.s.val := Nat.succ_le_of_lt phase.ha_lt_s
      have hstrict : phase.a.val + 1 < phase.s.val := by
        apply Nat.lt_of_le_of_ne hsucc_le
        simpa [eq_comm] using hlen1
      omega
    rcases len2_phase_start_in_five_or_ec gc t phase hlen2 with hec | hll | hl | hr | hrr
    · exact Or.inl hec
    · right
      intro k hk1 hk2
      by_cases hk_a : k = phase.a
      · left
        simpa [hk_a] using hll
      · have hk_prev_val : k.val = phase.s.val - 1 := by omega
        have hgap2 : phase.s.val - phase.a.val ≥ 2 := by omega
        rcases pre_step_fires_neighbor gc t phase hgap2 with hprevL | hprevR | hprevT
        · right; left
          have hk_eq : k = ⟨phase.s.val - 1, by
              have := phase.ha_lt_s
              have := phase.s.isLt
              omega⟩ := Fin.ext hk_prev_val
          simpa [hk_eq] using hprevL
        · right; right; left
          have hk_eq : k = ⟨phase.s.val - 1, by
              have := phase.ha_lt_s
              have := phase.s.isLt
              omega⟩ := Fin.ext hk_prev_val
          simpa [hk_eq] using hprevR
        · have hk_eq : k = ⟨phase.s.val - 1, by
              have := phase.ha_lt_s
              have := phase.s.isLt
              omega⟩ := Fin.ext hk_prev_val
          exact False.elim (phase.ht_nofire k hk1 hk2 (by simpa [hk_eq] using hprevT))
    · right
      intro k hk1 hk2
      by_cases hk_a : k = phase.a
      · right; left
        simpa [hk_a] using hl
      · have hk_prev_val : k.val = phase.s.val - 1 := by omega
        have hgap2 : phase.s.val - phase.a.val ≥ 2 := by omega
        rcases pre_step_fires_neighbor gc t phase hgap2 with hprevL | hprevR | hprevT
        · right; left
          have hk_eq : k = ⟨phase.s.val - 1, by
              have := phase.ha_lt_s
              have := phase.s.isLt
              omega⟩ := Fin.ext hk_prev_val
          simpa [hk_eq] using hprevL
        · right; right; left
          have hk_eq : k = ⟨phase.s.val - 1, by
              have := phase.ha_lt_s
              have := phase.s.isLt
              omega⟩ := Fin.ext hk_prev_val
          simpa [hk_eq] using hprevR
        · have hk_eq : k = ⟨phase.s.val - 1, by
              have := phase.ha_lt_s
              have := phase.s.isLt
              omega⟩ := Fin.ext hk_prev_val
          exact False.elim (phase.ht_nofire k hk1 hk2 (by simpa [hk_eq] using hprevT))
    · right
      intro k hk1 hk2
      by_cases hk_a : k = phase.a
      · right; right; left
        simpa [hk_a] using hr
      · have hk_prev_val : k.val = phase.s.val - 1 := by omega
        have hgap2 : phase.s.val - phase.a.val ≥ 2 := by omega
        rcases pre_step_fires_neighbor gc t phase hgap2 with hprevL | hprevR | hprevT
        · right; left
          have hk_eq : k = ⟨phase.s.val - 1, by
              have := phase.ha_lt_s
              have := phase.s.isLt
              omega⟩ := Fin.ext hk_prev_val
          simpa [hk_eq] using hprevL
        · right; right; left
          have hk_eq : k = ⟨phase.s.val - 1, by
              have := phase.ha_lt_s
              have := phase.s.isLt
              omega⟩ := Fin.ext hk_prev_val
          simpa [hk_eq] using hprevR
        · have hk_eq : k = ⟨phase.s.val - 1, by
              have := phase.ha_lt_s
              have := phase.s.isLt
              omega⟩ := Fin.ext hk_prev_val
          exact False.elim (phase.ht_nofire k hk1 hk2 (by simpa [hk_eq] using hprevT))
    · right
      intro k hk1 hk2
      by_cases hk_a : k = phase.a
      · right; right; right
        simpa [hk_a] using hrr
      · have hk_prev_val : k.val = phase.s.val - 1 := by omega
        have hgap2 : phase.s.val - phase.a.val ≥ 2 := by omega
        rcases pre_step_fires_neighbor gc t phase hgap2 with hprevL | hprevR | hprevT
        · right; left
          have hk_eq : k = ⟨phase.s.val - 1, by
              have := phase.ha_lt_s
              have := phase.s.isLt
              omega⟩ := Fin.ext hk_prev_val
          simpa [hk_eq] using hprevL
        · right; right; left
          have hk_eq : k = ⟨phase.s.val - 1, by
              have := phase.ha_lt_s
              have := phase.s.isLt
              omega⟩ := Fin.ext hk_prev_val
          simpa [hk_eq] using hprevR
        · have hk_eq : k = ⟨phase.s.val - 1, by
              have := phase.ha_lt_s
              have := phase.s.isLt
              omega⟩ := Fin.ext hk_prev_val
          exact False.elim (phase.ht_nofire k hk1 hk2 (by simpa [hk_eq] using hprevT))

/-- Under global all-normality for a pivot `t`, every phase has a short suffix
    ending at the same `t`-fire whose movers are confined to the pivot's
    5-neighborhood, unless an entry conflict already appears. -/
theorem normal_phase_has_localized_short_suffix_or_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall_normal : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t) :
    hasEntryConflict gc ∨
    ∃ phase1 : TernaryPhase gc t,
      phase1.s = phase.s ∧
      phase1.s.val = phase1.a.val + 1 ∧
      (gc.moverAt phase1.a = left t ∨ gc.moverAt phase1.a = right t) ∧
      ∀ k : Fin gc.configs.length,
        phase1.a.val ≤ k.val → k.val < phase1.s.val →
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) := by
  obtain ⟨phase1, hs, hlen1, hnorm1, _⟩ :=
    normal_phase_has_len1_suffix gc t hall_normal phase
  rcases normal_phase_len_le2_localized_or_ec gc t phase1 hnorm1 (by omega) with hec | hloc
  · exact Or.inl hec
  · exact Or.inr ⟨phase1, hs, hlen1, normal_len1_phase_starts_at_neighbor gc t phase1 hnorm1 hlen1, hloc⟩

/-- In any fixed phase, either every mover already lies in the pivot's
    5-neighborhood `{left(left t), left t, right t, right(right t)}`, or there
    is a last step in the phase whose mover lies outside that neighborhood. -/
theorem phase_last_outside_or_all_local
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t) :
    (∀ k : Fin gc.configs.length,
      phase.a.val ≤ k.val → k.val < phase.s.val →
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t)) ∨
    ∃ a0 : Fin gc.configs.length,
      phase.a.val ≤ a0.val ∧
      a0.val < phase.s.val ∧
      gc.moverAt a0 ≠ left (left t) ∧
      gc.moverAt a0 ≠ left t ∧
      gc.moverAt a0 ≠ t ∧
      gc.moverAt a0 ≠ right t ∧
      gc.moverAt a0 ≠ right (right t) ∧
      ∀ k : Fin gc.configs.length,
        a0.val < k.val → k.val < phase.s.val →
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t ∨
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t) := by
  by_cases hall :
      ∀ k : Fin gc.configs.length,
        phase.a.val ≤ k.val → k.val < phase.s.val →
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t ∨
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t)
  · exact Or.inl hall
  · have hall' : ∃ k0 : Fin gc.configs.length,
        phase.a.val ≤ k0.val ∧
        k0.val < phase.s.val ∧
        ¬(gc.moverAt k0 = left (left t) ∨
          gc.moverAt k0 = left t ∨
          gc.moverAt k0 = right t ∨
          gc.moverAt k0 = right (right t)) := by
      simpa using hall
    obtain ⟨k0, hk0_ge, hk0_lt, hk0_bad⟩ := hall'
    have hk0_ll : gc.moverAt k0 ≠ left (left t) := by
      intro hk
      exact hk0_bad (Or.inl hk)
    have hk0_l : gc.moverAt k0 ≠ left t := by
      intro hk
      exact hk0_bad (Or.inr (Or.inl hk))
    have hk0_t : gc.moverAt k0 ≠ t := by
      exact phase.ht_nofire k0 hk0_ge hk0_lt
    have hk0_r : gc.moverAt k0 ≠ right t := by
      intro hk
      exact hk0_bad (Or.inr (Or.inr (Or.inl hk)))
    have hk0_rr : gc.moverAt k0 ≠ right (right t) := by
      intro hk
      exact hk0_bad (Or.inr (Or.inr (Or.inr hk)))
    let badSet : Finset (Fin gc.configs.length) :=
      (Finset.univ : Finset (Fin gc.configs.length)).filter
        (fun k =>
          phase.a.val ≤ k.val ∧
          k.val < phase.s.val ∧
          gc.moverAt k ≠ left (left t) ∧
          gc.moverAt k ≠ left t ∧
          gc.moverAt k ≠ t ∧
          gc.moverAt k ≠ right t ∧
          gc.moverAt k ≠ right (right t))
    have hk0_mem : k0 ∈ badSet := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ k0, ?_⟩
      exact ⟨hk0_ge, hk0_lt, hk0_ll, hk0_l, hk0_t, hk0_r, hk0_rr⟩
    have hbad_nonempty : badSet.Nonempty := ⟨k0, hk0_mem⟩
    obtain ⟨a0, ha0_mem, ha0_max⟩ := Finset.exists_max_image badSet Fin.val hbad_nonempty
    have ha0_props : a0 ∈ badSet := ha0_mem
    have ha0_ge : phase.a.val ≤ a0.val := by
      simp [badSet] at ha0_props
      exact ha0_props.1
    have ha0_lt : a0.val < phase.s.val := by
      simp [badSet] at ha0_props
      exact ha0_props.2.1
    have ha0_ll : gc.moverAt a0 ≠ left (left t) := by
      simp [badSet] at ha0_props
      exact ha0_props.2.2.1
    have ha0_l : gc.moverAt a0 ≠ left t := by
      simp [badSet] at ha0_props
      exact ha0_props.2.2.2.1
    have ha0_t : gc.moverAt a0 ≠ t := by
      simp [badSet] at ha0_props
      exact ha0_props.2.2.2.2.1
    have ha0_r : gc.moverAt a0 ≠ right t := by
      simp [badSet] at ha0_props
      exact ha0_props.2.2.2.2.2.1
    have ha0_rr : gc.moverAt a0 ≠ right (right t) := by
      simp [badSet] at ha0_props
      exact ha0_props.2.2.2.2.2.2
    refine Or.inr ⟨a0, ha0_ge, ha0_lt, ha0_ll, ha0_l, ha0_t, ha0_r, ha0_rr, ?_⟩
    intro k hak hk_lt
    by_contra hk_local
    have hk_ll : gc.moverAt k ≠ left (left t) := by
      intro hk_eq
      exact hk_local (Or.inl hk_eq)
    have hk_l : gc.moverAt k ≠ left t := by
      intro hk_eq
      exact hk_local (Or.inr (Or.inl hk_eq))
    have hk_t : gc.moverAt k ≠ t := by
      exact phase.ht_nofire k (le_trans ha0_ge (Nat.le_of_lt hak)) hk_lt
    have hk_r : gc.moverAt k ≠ right t := by
      intro hk_eq
      exact hk_local (Or.inr (Or.inr (Or.inl hk_eq)))
    have hk_rr : gc.moverAt k ≠ right (right t) := by
      intro hk_eq
      exact hk_local (Or.inr (Or.inr (Or.inr hk_eq)))
    have hk_mem : k ∈ badSet := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ k, ?_⟩
      exact ⟨le_trans ha0_ge (Nat.le_of_lt hak), hk_lt, hk_ll, hk_l, hk_t, hk_r, hk_rr⟩
    have := ha0_max k hk_mem
    omega

/-! ### Step 5c: Universal phase EC via Ring Alternation -/

/-- If moverAt k = p at some step k, then fireCount p > 0. -/
theorem fireCount_pos_of_moverAt_eq
    (gc : GoodCycle sys) (p : Fin sys.rs.n) (k : Fin gc.configs.length)
    (hmov : gc.moverAt k = p) :
    gc.fireCount p > 0 := by
  rw [gc.fireCount_eq_sum_moverAt]
  have h1 : (if gc.moverAt k = p then (1 : Nat) else 0) = 1 := by simp [hmov]
  have hle := Finset.single_le_sum (f := fun j => if gc.moverAt j = p then (1 : Nat) else 0)
    (fun j _ => by simp only; split <;> omega) (Finset.mem_univ k)
  simp only [h1] at hle; omega

/-- If processor p fires at every step (fireCount = L) and n ≥ 5, then
    there exists a safe processor, contradicting hno_safe.

    Proof: if all steps fire p, then any processor q at distance ≥ 2 from p
    is safe (moverAt k = p ≠ q, left q, right q). With n ≥ 5, such q exists. -/
theorem fireCount_lt_length_of_hno_safe
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 5)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (p : Fin sys.rs.n) :
    gc.fireCount p < gc.configs.length := by
  by_contra hge; push_neg at hge
  have hfc_le : gc.fireCount p ≤ gc.configs.length := by
    rw [gc.fireCount_eq_sum_moverAt p]
    calc (∑ j : Fin gc.configs.length, if gc.moverAt j = p then (1 : Nat) else 0)
        ≤ ∑ j : Fin gc.configs.length, 1 :=
          Finset.sum_le_sum (fun j _ => by split <;> omega)
      _ = gc.configs.length := by simp
  have hfc_eq : gc.fireCount p = gc.configs.length := by omega
  have hall_p : ∀ k : Fin gc.configs.length, gc.moverAt k = p := by
    by_contra hnot; push_neg at hnot; obtain ⟨k₀, hk₀⟩ := hnot
    rw [gc.fireCount_eq_sum_moverAt p] at hfc_eq
    have hlt : (∑ j : Fin gc.configs.length, if gc.moverAt j = p then (1 : Nat) else 0) <
        ∑ j : Fin gc.configs.length, 1 :=
      Finset.sum_lt_sum (fun j _ => by split <;> omega)
        ⟨k₀, Finset.mem_univ k₀, by simp [hk₀]⟩
    have hsum1 : ∑ j : Fin gc.configs.length, (1 : Nat) = gc.configs.length := by
      simp [Finset.sum_const, Finset.card_fin]
    rw [hsum1] at hlt; omega
  exfalso; apply hno_safe
  have hcard : (Finset.univ : Finset (Fin sys.rs.n)).card = sys.rs.n := Finset.card_fin _
  have : ∃ q : Fin sys.rs.n, q ∉ ({p, left p, right p} : Finset (Fin sys.rs.n)) := by
    by_contra hall; push_neg at hall
    have hsub : Finset.univ ⊆ ({p, left p, right p} : Finset (Fin sys.rs.n)) :=
      fun x _ => hall x
    have hle := Finset.card_le_card hsub; rw [hcard] at hle
    have : ({p, left p, right p} : Finset (Fin sys.rs.n)).card ≤ 3 := by
      calc ({p, left p, right p} : Finset _).card
          ≤ ({p} ∪ {left p} ∪ {right p} : Finset _).card := by
            apply Finset.card_le_card; intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            simp only [Finset.mem_union, Finset.mem_singleton]
            rcases hx with rfl | rfl | rfl <;> simp
        _ ≤ ({p} ∪ {left p} : Finset _).card + ({right p} : Finset _).card :=
            Finset.card_union_le _ _
        _ ≤ (({p} : Finset _).card + ({left p} : Finset _).card) + ({right p} : Finset _).card := by
            linarith [Finset.card_union_le ({p} : Finset _) {left p}]
        _ = 3 := by simp
    omega
  obtain ⟨q, hq⟩ := this
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
  obtain ⟨hq_ne_p, hq_ne_lp, hq_ne_rp⟩ := hq
  have h_ne_q : p ≠ q := Ne.symm hq_ne_p
  have h_ne_lq : left q ≠ p := by
    intro hlq; apply hq_ne_rp
    have : right (left q) = right p := congrArg right hlq
    rwa [right_left_eq_self] at this
  have h_ne_rq : right q ≠ p := by
    intro hrq; apply hq_ne_lp
    have : left (right q) = left p := congrArg left hrq
    rwa [left_right_eq_self] at this
  exact ⟨q, fun k => ⟨by rw [hall_p k]; exact h_ne_q,
                        by rw [hall_p k]; exact Ne.symm h_ne_lq,
                        by rw [hall_p k]; exact Ne.symm h_ne_rq⟩⟩

/-! ### Palindromic Entry Conflict (shared core argument) -/

/-- If all movers are in {p, left p, right p} and n ≥ 7, then a safe
    processor exists, contradicting hno_safe.

    Proof: {p, left p, right p, left(left p), right(right p)} has at most
    5 elements. With n ≥ 7, there exists q outside this 5-set. Then
    {q, left q, right q} ∩ {p, left p, right p} = ∅, making q safe. -/
theorem movers_in_triple_contradicts_hno_safe
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (p : Fin sys.rs.n)
    (hall : ∀ k : Fin gc.configs.length,
      gc.moverAt k = p ∨ gc.moverAt k = left p ∨ gc.moverAt k = right p) :
    False := by
  apply hno_safe
  -- Need q ∉ {p, lp, rp, llp, rrp}
  have hcard : (Finset.univ : Finset (Fin sys.rs.n)).card = sys.rs.n := Finset.card_fin _
  -- The set {p, lp, rp, llp, rrp} has at most 5 elements
  set S5 := ({p, left p, right p, left (left p), right (right p)} : Finset (Fin sys.rs.n))
  have hS5_le : S5.card ≤ 5 := by
    have h1 : S5 ⊆ {p, left p, right p, left (left p), right (right p)} := Finset.Subset.refl _
    calc S5.card
        ≤ ({p, left p, right p, left (left p), right (right p)} : Finset _).card := Finset.card_le_card h1
      _ ≤ 5 := by
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          simp [Finset.card_singleton]
  have : ∃ q : Fin sys.rs.n, q ∉ S5 := by
    by_contra hall_in; push_neg at hall_in
    have hsub : Finset.univ ⊆ S5 := fun x _ => hall_in x
    have hle := Finset.card_le_card hsub; rw [hcard] at hle; omega
  obtain ⟨q, hq⟩ := this
  simp only [S5, Finset.mem_insert, Finset.mem_singleton, not_or] at hq
  obtain ⟨hq_ne_p, hq_ne_lp, hq_ne_rp, hq_ne_llp, hq_ne_rrp⟩ := hq
  -- q is safe: for all k, moverAt k ∉ {q, left q, right q}
  refine ⟨q, fun k => ?_⟩
  rcases hall k with hmov | hmov | hmov <;> rw [hmov]
  · -- moverAt k = p. Need: p ≠ q ∧ p ≠ left q ∧ p ≠ right q
    refine ⟨Ne.symm hq_ne_p, ?_, ?_⟩
    · intro h; apply hq_ne_rp
      have := congrArg right h.symm; rwa [right_left_eq_self] at this
    · intro h; apply hq_ne_lp
      have := congrArg left h.symm; rwa [left_right_eq_self] at this
  · -- moverAt k = left p. Need: left p ≠ q ∧ left p ≠ left q ∧ left p ≠ right q
    refine ⟨Ne.symm hq_ne_lp, ?_, ?_⟩
    · intro h; apply hq_ne_p
      have := congrArg right h.symm; rwa [right_left_eq_self, right_left_eq_self] at this
    · intro h; apply hq_ne_llp
      have := congrArg left h.symm; rwa [left_right_eq_self] at this
  · -- moverAt k = right p. Need: right p ≠ q ∧ right p ≠ left q ∧ right p ≠ right q
    refine ⟨Ne.symm hq_ne_rp, ?_, ?_⟩
    · intro h; apply hq_ne_rrp
      have := congrArg right h.symm; rwa [right_left_eq_self] at this
    · intro h; apply hq_ne_p
      have := congrArg left h.symm; rwa [left_right_eq_self, left_right_eq_self] at this

/-- If all movers are in the 5-set
    `{left(left p), left p, p, right p, right(right p)}` and `n ≥ 7`,
    then a safe processor exists, contradicting `hno_safe`.

    Proof: choose `q` outside the surrounding 7-set
    `{left^3 p, left^2 p, left p, p, right p, right^2 p, right^3 p}`.
    Then `{q, left q, right q}` is disjoint from the 5-set. -/
theorem movers_in_five_contradicts_hno_safe
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 8)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (p : Fin sys.rs.n)
    (hall : ∀ k : Fin gc.configs.length,
      gc.moverAt k = left (left p) ∨
      gc.moverAt k = left p ∨
      gc.moverAt k = p ∨
      gc.moverAt k = right p ∨
      gc.moverAt k = right (right p)) :
    False := by
  apply hno_safe
  have hcard : (Finset.univ : Finset (Fin sys.rs.n)).card = sys.rs.n := Finset.card_fin _
  set S7 := ({left (left (left p)), left (left p), left p, p,
    right p, right (right p), right (right (right p))} : Finset (Fin sys.rs.n))
  have hS7_le : S7.card ≤ 7 := by
    have h1 : S7 ⊆ {left (left (left p)), left (left p), left p, p,
        right p, right (right p), right (right (right p))} := Finset.Subset.refl _
    calc S7.card
        ≤ ({left (left (left p)), left (left p), left p, p,
            right p, right (right p), right (right (right p))} : Finset _).card :=
          Finset.card_le_card h1
      _ ≤ 7 := by
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          simp [Finset.card_singleton]
  have : ∃ q : Fin sys.rs.n, q ∉ S7 := by
    by_contra hall_in; push_neg at hall_in
    have hsub : Finset.univ ⊆ S7 := fun x _ => hall_in x
    have hle := Finset.card_le_card hsub
    rw [hcard] at hle
    omega
  obtain ⟨q, hq⟩ := this
  simp only [S7, Finset.mem_insert, Finset.mem_singleton, not_or] at hq
  obtain ⟨hq_ne_lllp, hq_ne_llp, hq_ne_lp, hq_ne_p,
    hq_ne_rp, hq_ne_rrp, hq_ne_rrrp⟩ := hq
  refine ⟨q, fun k => ?_⟩
  rcases hall k with hmov | hmov | hmov | hmov | hmov <;> rw [hmov]
  · refine ⟨Ne.symm hq_ne_llp, ?_, ?_⟩
    · intro h
      apply hq_ne_lp
      have := congrArg right h.symm
      rwa [right_left_eq_self, right_left_eq_self] at this
    · intro h
      apply hq_ne_lllp
      have := congrArg left h.symm
      rwa [left_right_eq_self] at this
  · refine ⟨Ne.symm hq_ne_lp, ?_, ?_⟩
    · intro h
      apply hq_ne_p
      have := congrArg right h.symm
      simpa [right_left_eq_self] using this
    · intro h
      apply hq_ne_llp
      have := congrArg left h.symm
      simpa [left_right_eq_self] using this
  · refine ⟨Ne.symm hq_ne_p, ?_, ?_⟩
    · intro h
      apply hq_ne_rp
      have := congrArg right h.symm
      rwa [right_left_eq_self] at this
    · intro h
      apply hq_ne_lp
      have := congrArg left h.symm
      rwa [left_right_eq_self] at this
  · refine ⟨Ne.symm hq_ne_rp, ?_, ?_⟩
    · intro h
      apply hq_ne_rrp
      have := congrArg right h.symm
      simpa [right_left_eq_self] using this
    · intro h
      apply hq_ne_p
      have := congrArg left h.symm
      simpa [left_right_eq_self] using this
  · refine ⟨Ne.symm hq_ne_rrp, ?_, ?_⟩
    · intro h
      apply hq_ne_rrrp
      have := congrArg right h.symm
      simpa [right_left_eq_self] using this
    · intro h
      apply hq_ne_rp
      have := congrArg left h.symm
      simpa [left_right_eq_self] using this

/-- If all movers stay in the left-biased 6-set
    `{left^3 p, left^2 p, left p, p, right p, right^2 p}`, then a safe
    processor exists for `n ≥ 7`. -/
theorem movers_in_left_six_contradicts_hno_safe
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (p : Fin sys.rs.n)
    (hall : ∀ k : Fin gc.configs.length,
      gc.moverAt k = left (left (left p)) ∨
      gc.moverAt k = left (left p) ∨
      gc.moverAt k = left p ∨
      gc.moverAt k = p ∨
      gc.moverAt k = right p ∨
      gc.moverAt k = right (right p)) :
    False := by
  apply hno_safe
  have hcard : (Finset.univ : Finset (Fin sys.rs.n)).card = sys.rs.n := Finset.card_fin _
  set S8 := ({left (left (left (left p))), left (left (left p)),
    left (left p), left p, p, right p, right (right p), right (right (right p))} :
      Finset (Fin sys.rs.n))
  have hS8_le : S8.card ≤ 8 := by
    have h1 : S8 ⊆ {left (left (left (left p))), left (left (left p)),
        left (left p), left p, p, right p, right (right p), right (right (right p))} :=
      Finset.Subset.refl _
    calc S8.card
        ≤ ({left (left (left (left p))), left (left (left p)),
            left (left p), left p, p, right p, right (right p),
            right (right (right p))} : Finset _).card := Finset.card_le_card h1
      _ ≤ 8 := by
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          simp [Finset.card_singleton]
  have : ∃ q : Fin sys.rs.n, q ∉ S8 := by
    by_contra hall_in
    push_neg at hall_in
    have hsub : Finset.univ ⊆ S8 := fun x _ => hall_in x
    have hle := Finset.card_le_card hsub
    rw [hcard] at hle
    omega
  obtain ⟨q, hq⟩ := this
  simp only [S8, Finset.mem_insert, Finset.mem_singleton, not_or] at hq
  obtain ⟨hq_ne_l4p, hq_ne_l3p, hq_ne_l2p, hq_ne_lp, hq_ne_p, hq_ne_rp, hq_ne_r2p, hq_ne_r3p⟩ := hq
  refine ⟨q, fun k => ?_⟩
  rcases hall k with hmov | hmov | hmov | hmov | hmov | hmov <;> rw [hmov]
  · refine ⟨Ne.symm hq_ne_l3p, ?_, ?_⟩
    · intro h
      apply hq_ne_l2p
      have := congrArg right h.symm
      simpa [right_left_eq_self] using this
    · intro h
      apply hq_ne_l4p
      have := congrArg left h.symm
      simpa [left_right_eq_self] using this
  · refine ⟨Ne.symm hq_ne_l2p, ?_, ?_⟩
    · intro h
      apply hq_ne_lp
      have := congrArg right h.symm
      simpa [right_left_eq_self] using this
    · intro h
      apply hq_ne_l3p
      have := congrArg left h.symm
      simpa [left_right_eq_self] using this
  · refine ⟨Ne.symm hq_ne_lp, ?_, ?_⟩
    · intro h
      apply hq_ne_p
      have := congrArg right h.symm
      simpa [right_left_eq_self, right_left_eq_self] using this
    · intro h
      apply hq_ne_l2p
      have := congrArg left h.symm
      simpa [left_right_eq_self] using this
  · refine ⟨Ne.symm hq_ne_p, ?_, ?_⟩
    · intro h
      apply hq_ne_rp
      have := congrArg right h.symm
      simpa [right_left_eq_self] using this
    · intro h
      apply hq_ne_lp
      have := congrArg left h.symm
      simpa [left_right_eq_self] using this
  · refine ⟨Ne.symm hq_ne_rp, ?_, ?_⟩
    · intro h
      apply hq_ne_r2p
      have := congrArg right h.symm
      simpa [right_left_eq_self] using this
    · intro h
      apply hq_ne_p
      have := congrArg left h.symm
      simpa [left_right_eq_self, left_right_eq_self] using this
  · refine ⟨Ne.symm hq_ne_r2p, ?_, ?_⟩
    · intro h
      apply hq_ne_r3p
      have := congrArg right h.symm
      simpa [right_left_eq_self] using this
    · intro h
      apply hq_ne_rp
      have := congrArg left h.symm
      simpa [left_right_eq_self] using this

/-- Symmetric right-sided 6-set safe-processor lemma. -/
theorem movers_in_right_six_contradicts_hno_safe
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (p : Fin sys.rs.n)
    (hall : ∀ k : Fin gc.configs.length,
      gc.moverAt k = left (left p) ∨
      gc.moverAt k = left p ∨
      gc.moverAt k = p ∨
      gc.moverAt k = right p ∨
      gc.moverAt k = right (right p) ∨
      gc.moverAt k = right (right (right p))) :
    False := by
  apply hno_safe
  have hcard : (Finset.univ : Finset (Fin sys.rs.n)).card = sys.rs.n := Finset.card_fin _
  set S8 := ({left (left (left p)), left (left p), left p, p, right p,
    right (right p), right (right (right p)), right (right (right (right p)))} :
      Finset (Fin sys.rs.n))
  have hS8_le : S8.card ≤ 8 := by
    have h1 : S8 ⊆ {left (left (left p)), left (left p), left p, p, right p,
        right (right p), right (right (right p)), right (right (right (right p)))} :=
      Finset.Subset.refl _
    calc S8.card
        ≤ ({left (left (left p)), left (left p), left p, p, right p,
            right (right p), right (right (right p)),
            right (right (right (right p)))} : Finset _).card := Finset.card_le_card h1
      _ ≤ 8 := by
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          apply le_trans (Finset.card_insert_le _ _)
          simp only [Nat.succ_le_succ_iff]
          simp [Finset.card_singleton]
  have : ∃ q : Fin sys.rs.n, q ∉ S8 := by
    by_contra hall_in
    push_neg at hall_in
    have hsub : Finset.univ ⊆ S8 := fun x _ => hall_in x
    have hle := Finset.card_le_card hsub
    rw [hcard] at hle
    omega
  obtain ⟨q, hq⟩ := this
  simp only [S8, Finset.mem_insert, Finset.mem_singleton, not_or] at hq
  obtain ⟨hq_ne_l3p, hq_ne_l2p, hq_ne_lp, hq_ne_p, hq_ne_rp, hq_ne_r2p, hq_ne_r3p, hq_ne_r4p⟩ := hq
  refine ⟨q, fun k => ?_⟩
  rcases hall k with hmov | hmov | hmov | hmov | hmov | hmov <;> rw [hmov]
  · refine ⟨Ne.symm hq_ne_l2p, ?_, ?_⟩
    · intro h
      apply hq_ne_lp
      have := congrArg right h.symm
      simpa [right_left_eq_self] using this
    · intro h
      apply hq_ne_l3p
      have := congrArg left h.symm
      simpa [left_right_eq_self] using this
  · refine ⟨Ne.symm hq_ne_lp, ?_, ?_⟩
    · intro h
      apply hq_ne_p
      have := congrArg right h.symm
      simpa [right_left_eq_self, right_left_eq_self] using this
    · intro h
      apply hq_ne_l2p
      have := congrArg left h.symm
      simpa [left_right_eq_self] using this
  · refine ⟨Ne.symm hq_ne_p, ?_, ?_⟩
    · intro h
      apply hq_ne_rp
      have := congrArg right h.symm
      simpa [right_left_eq_self] using this
    · intro h
      apply hq_ne_lp
      have := congrArg left h.symm
      simpa [left_right_eq_self] using this
  · refine ⟨Ne.symm hq_ne_rp, ?_, ?_⟩
    · intro h
      apply hq_ne_r2p
      have := congrArg right h.symm
      simpa [right_left_eq_self] using this
    · intro h
      apply hq_ne_p
      have := congrArg left h.symm
      simpa [left_right_eq_self, left_right_eq_self] using this
  · refine ⟨Ne.symm hq_ne_r2p, ?_, ?_⟩
    · intro h
      apply hq_ne_r3p
      have := congrArg right h.symm
      simpa [right_left_eq_self] using this
    · intro h
      apply hq_ne_rp
      have := congrArg left h.symm
      simpa [left_right_eq_self] using this
  · refine ⟨Ne.symm hq_ne_r3p, ?_, ?_⟩
    · intro h
      apply hq_ne_r4p
      have := congrArg right h.symm
      simpa [right_left_eq_self] using this
    · intro h
      apply hq_ne_r2p
      have := congrArg left h.symm
      simpa [left_right_eq_self] using this

/-- If `a0` is the last globally outside mover and it sits at `left^3(t)` or
    `right^3(t)`, then every later mover lies in the corresponding 6-neighborhood
    around `t`. -/
theorem last_outside_suffix_in_left_or_right_six
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (a0 : Fin gc.configs.length)
    (ha0_side :
      gc.moverAt a0 = left (left (left t)) ∨
      gc.moverAt a0 = right (right (right t)))
    (hlater_local : ∀ k : Fin gc.configs.length,
      a0.val < k.val →
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t)) :
    (∀ k : Fin gc.configs.length,
      a0.val ≤ k.val →
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t)) ∨
    (∀ k : Fin gc.configs.length,
      a0.val ≤ k.val →
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t))) := by
  rcases ha0_side with ha0_left | ha0_right
  · left
    intro k hk_ge
    by_cases hk_eq : k = a0
    · subst hk_eq
      exact Or.inl ha0_left
    · have hk_gt : a0.val < k.val := by
        have hneq_val : k.val ≠ a0.val := by
          intro hval
          exact hk_eq (Fin.ext hval)
        omega
      rcases hlater_local k hk_gt with hkll | hkl | hkt | hkr | hkrr
      · exact Or.inr (Or.inl hkll)
      · exact Or.inr (Or.inr (Or.inl hkl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hkt)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hkr))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hkrr))))
  · right
    intro k hk_ge
    by_cases hk_eq : k = a0
    · subst hk_eq
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ha0_right))))
    · have hk_gt : a0.val < k.val := by
        have hneq_val : k.val ≠ a0.val := by
          intro hval
          exact hk_eq (Fin.ext hval)
        omega
      rcases hlater_local k hk_gt with hkll | hkl | hkt | hkr | hkrr
      · exact Or.inl hkll
      · exact Or.inr (Or.inl hkl)
      · exact Or.inr (Or.inr (Or.inl hkt))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hkr)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hkrr))))

/-- If every mover after `j` lies in the left-biased 6-neighborhood and
    `k_out` is a later mover that is still outside the pivot's local 5-set,
    then `k_out` must be exactly `left^3(t)`. -/
theorem outside_of_left_six_tail_eq_left3
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (j k_out : Fin gc.configs.length)
    (hj_lt : j.val < k_out.val)
    (hk_outside :
      gc.moverAt k_out ≠ left (left t) ∧
      gc.moverAt k_out ≠ left t ∧
      gc.moverAt k_out ≠ t ∧
      gc.moverAt k_out ≠ right t ∧
      gc.moverAt k_out ≠ right (right t))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t)) :
    gc.moverAt k_out = left (left (left t)) := by
  have hk_tail := hj_tail k_out hj_lt
  rcases hk_tail with hk | hk | hk | hk | hk | hk
  · exact hk
  · exact False.elim (hk_outside.1 hk)
  · exact False.elim (hk_outside.2.1 hk)
  · exact False.elim (hk_outside.2.2.1 hk)
  · exact False.elim (hk_outside.2.2.2.1 hk)
  · exact False.elim (hk_outside.2.2.2.2 hk)

/-- If every mover after `j` lies in the right-biased 6-neighborhood and
    `k_out` is a later mover that is still outside the pivot's local 5-set,
    then `k_out` must be exactly `right^3(t)`. -/
theorem outside_of_right_six_tail_eq_right3
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (j k_out : Fin gc.configs.length)
    (hj_lt : j.val < k_out.val)
    (hk_outside :
      gc.moverAt k_out ≠ left (left t) ∧
      gc.moverAt k_out ≠ left t ∧
      gc.moverAt k_out ≠ t ∧
      gc.moverAt k_out ≠ right t ∧
      gc.moverAt k_out ≠ right (right t))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t))) :
    gc.moverAt k_out = right (right (right t)) := by
  have hk_tail := hj_tail k_out hj_lt
  rcases hk_tail with hk | hk | hk | hk | hk | hk
  · exact False.elim (hk_outside.1 hk)
  · exact False.elim (hk_outside.2.1 hk)
  · exact False.elim (hk_outside.2.2.1 hk)
  · exact False.elim (hk_outside.2.2.2.1 hk)
  · exact False.elim (hk_outside.2.2.2.2 hk)
  · exact hk

/-- If an outside mover is immediately followed by a mover in the pivot's
    5-neighborhood, then the outside mover must be exactly `left^3(t)` or
    `right^3(t)`. -/
theorem outside_step_followed_by_local_five_forces_side
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (a0 a1 : Fin gc.configs.length)
    (hnext : nextIndex gc.configs a0 = a1)
    (ha0_out :
      gc.moverAt a0 ≠ left (left t) ∧
      gc.moverAt a0 ≠ left t ∧
      gc.moverAt a0 ≠ t ∧
      gc.moverAt a0 ≠ right t ∧
      gc.moverAt a0 ≠ right (right t))
    (ha1_local :
      gc.moverAt a1 = left (left t) ∨
      gc.moverAt a1 = left t ∨
      gc.moverAt a1 = t ∨
      gc.moverAt a1 = right t ∨
      gc.moverAt a1 = right (right t)) :
    gc.moverAt a0 = left (left (left t)) ∨
    gc.moverAt a0 = right (right (right t)) := by
  have hnext_local := gc.next_mover_is_local a0
  rw [hnext] at hnext_local
  rcases ha1_local with ha1_ll | ha1_l | ha1_t | ha1_r | ha1_rr
  · rcases hnext_local with hleft | hself | hright
    · exfalso
      have : gc.moverAt a0 = left t := by
        have htmp : left t = gc.moverAt a0 := by
          simpa [ha1_ll, right_left_eq_self] using congrArg right hleft
        exact htmp.symm
      exact ha0_out.2.1 this
    · exfalso
      exact ha0_out.1 (by simpa [ha1_ll] using hself.symm)
    · have htmp : left (left (left t)) = gc.moverAt a0 := by
        simpa [ha1_ll, left_right_eq_self] using congrArg left hright
      exact Or.inl htmp.symm
  · rcases hnext_local with hleft | hself | hright
    · exfalso
      have : gc.moverAt a0 = t := by
        have htmp : t = gc.moverAt a0 := by
          simpa [ha1_l, right_left_eq_self] using congrArg right hleft
        exact htmp.symm
      exact ha0_out.2.2.1 this
    · exfalso
      exact ha0_out.2.1 (by simpa [ha1_l] using hself.symm)
    · exfalso
      have : gc.moverAt a0 = left (left t) := by
        have htmp : left (left t) = gc.moverAt a0 := by
          simpa [ha1_l, left_right_eq_self] using congrArg left hright
        exact htmp.symm
      exact ha0_out.1 this
  · rcases hnext_local with hleft | hself | hright
    · exfalso
      have : gc.moverAt a0 = right t := by
        have htmp : right t = gc.moverAt a0 := by
          simpa [ha1_t, right_left_eq_self] using congrArg right hleft
        exact htmp.symm
      exact ha0_out.2.2.2.1 this
    · exfalso
      exact ha0_out.2.2.1 (by simpa [ha1_t] using hself.symm)
    · exfalso
      have : gc.moverAt a0 = left t := by
        have htmp : left t = gc.moverAt a0 := by
          simpa [ha1_t, left_right_eq_self] using congrArg left hright
        exact htmp.symm
      exact ha0_out.2.1 this
  · rcases hnext_local with hleft | hself | hright
    · exfalso
      have : gc.moverAt a0 = right (right t) := by
        have htmp : right (right t) = gc.moverAt a0 := by
          simpa [ha1_r, right_left_eq_self] using congrArg right hleft
        exact htmp.symm
      exact ha0_out.2.2.2.2 this
    · exfalso
      exact ha0_out.2.2.2.1 (by simpa [ha1_r] using hself.symm)
    · exfalso
      have : gc.moverAt a0 = t := by
        have htmp : t = gc.moverAt a0 := by
          simpa [ha1_r, left_right_eq_self] using congrArg left hright
        exact htmp.symm
      exact ha0_out.2.2.1 this
  · rcases hnext_local with hleft | hself | hright
    · have htmp : right (right (right t)) = gc.moverAt a0 := by
        simpa [ha1_rr, right_left_eq_self] using congrArg right hleft
      exact Or.inr htmp.symm
    · exfalso
      exact ha0_out.2.2.2.2 (by simpa [ha1_rr] using hself.symm)
    · exfalso
      have : gc.moverAt a0 = right t := by
        have htmp : right t = gc.moverAt a0 := by
          simpa [ha1_rr, left_right_eq_self] using congrArg left hright
        exact htmp.symm
      exact ha0_out.2.2.2.1 this

/-- If a mover outside the left-biased 6-neighborhood is immediately followed
    by a mover inside that 6-neighborhood, then the outside mover must be
    exactly `left^4(t)` or `right^3(t)`. -/
private theorem outside_step_followed_by_left_six_forces_edge
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (a0 a1 : Fin gc.configs.length)
    (hnext : nextIndex gc.configs a0 = a1)
    (ha0_out :
      gc.moverAt a0 ≠ left (left (left t)) ∧
      gc.moverAt a0 ≠ left (left t) ∧
      gc.moverAt a0 ≠ left t ∧
      gc.moverAt a0 ≠ t ∧
      gc.moverAt a0 ≠ right t ∧
      gc.moverAt a0 ≠ right (right t))
    (ha1_local :
      gc.moverAt a1 = left (left (left t)) ∨
      gc.moverAt a1 = left (left t) ∨
      gc.moverAt a1 = left t ∨
      gc.moverAt a1 = t ∨
      gc.moverAt a1 = right t ∨
      gc.moverAt a1 = right (right t)) :
    gc.moverAt a0 = left (left (left (left t))) ∨
    gc.moverAt a0 = right (right (right t)) := by
  have hnext_local := gc.next_mover_is_local a0
  rw [hnext] at hnext_local
  rcases ha1_local with ha1_l3 | ha1_l2 | ha1_l1 | ha1_t | ha1_r1 | ha1_r2
  · rcases hnext_local with hleft | hself | hright
    · exfalso
      have : gc.moverAt a0 = left (left t) := by
        have htmp : left (left t) = gc.moverAt a0 := by
          simpa [ha1_l3, right_left_eq_self] using congrArg right hleft
        exact htmp.symm
      exact ha0_out.2.1 this
    · exfalso
      exact ha0_out.1 (by simpa [ha1_l3] using hself.symm)
    · have htmp : left (left (left (left t))) = gc.moverAt a0 := by
        simpa [ha1_l3, left_right_eq_self] using congrArg left hright
      exact Or.inl htmp.symm
  · rcases hnext_local with hleft | hself | hright
    · exfalso
      have : gc.moverAt a0 = left t := by
        have htmp : left t = gc.moverAt a0 := by
          simpa [ha1_l2, right_left_eq_self] using congrArg right hleft
        exact htmp.symm
      exact ha0_out.2.2.1 this
    · exfalso
      exact ha0_out.2.1 (by simpa [ha1_l2] using hself.symm)
    · exfalso
      have : gc.moverAt a0 = left (left (left t)) := by
        have htmp : left (left (left t)) = gc.moverAt a0 := by
          simpa [ha1_l2, left_right_eq_self] using congrArg left hright
        exact htmp.symm
      exact ha0_out.1 this
  · rcases hnext_local with hleft | hself | hright
    · exfalso
      have : gc.moverAt a0 = t := by
        have htmp : t = gc.moverAt a0 := by
          simpa [ha1_l1, right_left_eq_self] using congrArg right hleft
        exact htmp.symm
      exact ha0_out.2.2.2.1 this
    · exfalso
      exact ha0_out.2.2.1 (by simpa [ha1_l1] using hself.symm)
    · exfalso
      have : gc.moverAt a0 = left (left t) := by
        have htmp : left (left t) = gc.moverAt a0 := by
          simpa [ha1_l1, left_right_eq_self] using congrArg left hright
        exact htmp.symm
      exact ha0_out.2.1 this
  · rcases hnext_local with hleft | hself | hright
    · exfalso
      have : gc.moverAt a0 = right t := by
        have htmp : right t = gc.moverAt a0 := by
          simpa [ha1_t, right_left_eq_self] using congrArg right hleft
        exact htmp.symm
      exact ha0_out.2.2.2.2.1 this
    · exfalso
      exact ha0_out.2.2.2.1 (by simpa [ha1_t] using hself.symm)
    · exfalso
      have : gc.moverAt a0 = left t := by
        have htmp : left t = gc.moverAt a0 := by
          simpa [ha1_t, left_right_eq_self] using congrArg left hright
        exact htmp.symm
      exact ha0_out.2.2.1 this
  · rcases hnext_local with hleft | hself | hright
    · exfalso
      have : gc.moverAt a0 = right (right t) := by
        have htmp : right (right t) = gc.moverAt a0 := by
          simpa [ha1_r1, right_left_eq_self] using congrArg right hleft
        exact htmp.symm
      exact ha0_out.2.2.2.2.2 this
    · exfalso
      exact ha0_out.2.2.2.2.1 (by simpa [ha1_r1] using hself.symm)
    · exfalso
      have : gc.moverAt a0 = t := by
        have htmp : t = gc.moverAt a0 := by
          simpa [ha1_r1, left_right_eq_self] using congrArg left hright
        exact htmp.symm
      exact ha0_out.2.2.2.1 this
  · rcases hnext_local with hleft | hself | hright
    · have htmp : right (right (right t)) = gc.moverAt a0 := by
        simpa [ha1_r2, right_left_eq_self] using congrArg right hleft
      exact Or.inr htmp.symm
    · exfalso
      exact ha0_out.2.2.2.2.2 (by simpa [ha1_r2] using hself.symm)
    · exfalso
      have : gc.moverAt a0 = right t := by
        have htmp : right t = gc.moverAt a0 := by
          simpa [ha1_r2, left_right_eq_self] using congrArg left hright
        exact htmp.symm
      exact ha0_out.2.2.2.2.1 this

/-- Symmetric right-biased 6-neighborhood predecessor lemma. -/
private theorem outside_step_followed_by_right_six_forces_edge
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (a0 a1 : Fin gc.configs.length)
    (hnext : nextIndex gc.configs a0 = a1)
    (ha0_out :
      gc.moverAt a0 ≠ left (left t) ∧
      gc.moverAt a0 ≠ left t ∧
      gc.moverAt a0 ≠ t ∧
      gc.moverAt a0 ≠ right t ∧
      gc.moverAt a0 ≠ right (right t) ∧
      gc.moverAt a0 ≠ right (right (right t)))
    (ha1_local :
      gc.moverAt a1 = left (left t) ∨
      gc.moverAt a1 = left t ∨
      gc.moverAt a1 = t ∨
      gc.moverAt a1 = right t ∨
      gc.moverAt a1 = right (right t) ∨
      gc.moverAt a1 = right (right (right t))) :
    gc.moverAt a0 = left (left (left t)) ∨
    gc.moverAt a0 = right (right (right (right t))) := by
  have hnext_local := gc.next_mover_is_local a0
  rw [hnext] at hnext_local
  rcases ha1_local with ha1_l2 | ha1_l1 | ha1_t | ha1_r1 | ha1_r2 | ha1_r3
  · rcases hnext_local with hleft | hself | hright
    · exfalso
      have : gc.moverAt a0 = left t := by
        have htmp : left t = gc.moverAt a0 := by
          simpa [ha1_l2, right_left_eq_self] using congrArg right hleft
        exact htmp.symm
      exact ha0_out.2.1 this
    · exfalso
      exact ha0_out.1 (by simpa [ha1_l2] using hself.symm)
    · have htmp : left (left (left t)) = gc.moverAt a0 := by
        simpa [ha1_l2, left_right_eq_self] using congrArg left hright
      exact Or.inl htmp.symm
  · rcases hnext_local with hleft | hself | hright
    · exfalso
      have : gc.moverAt a0 = t := by
        have htmp : t = gc.moverAt a0 := by
          simpa [ha1_l1, right_left_eq_self] using congrArg right hleft
        exact htmp.symm
      exact ha0_out.2.2.1 this
    · exfalso
      exact ha0_out.2.1 (by simpa [ha1_l1] using hself.symm)
    · exfalso
      have : gc.moverAt a0 = left (left t) := by
        have htmp : left (left t) = gc.moverAt a0 := by
          simpa [ha1_l1, left_right_eq_self] using congrArg left hright
        exact htmp.symm
      exact ha0_out.1 this
  · rcases hnext_local with hleft | hself | hright
    · exfalso
      have : gc.moverAt a0 = right t := by
        have htmp : right t = gc.moverAt a0 := by
          simpa [ha1_t, right_left_eq_self] using congrArg right hleft
        exact htmp.symm
      exact ha0_out.2.2.2.1 this
    · exfalso
      exact ha0_out.2.2.1 (by simpa [ha1_t] using hself.symm)
    · exfalso
      have : gc.moverAt a0 = left t := by
        have htmp : left t = gc.moverAt a0 := by
          simpa [ha1_t, left_right_eq_self] using congrArg left hright
        exact htmp.symm
      exact ha0_out.2.1 this
  · rcases hnext_local with hleft | hself | hright
    · exfalso
      have : gc.moverAt a0 = right (right t) := by
        have htmp : right (right t) = gc.moverAt a0 := by
          simpa [ha1_r1, right_left_eq_self] using congrArg right hleft
        exact htmp.symm
      exact ha0_out.2.2.2.2.1 this
    · exfalso
      exact ha0_out.2.2.2.1 (by simpa [ha1_r1] using hself.symm)
    · exfalso
      have : gc.moverAt a0 = t := by
        have htmp : t = gc.moverAt a0 := by
          simpa [ha1_r1, left_right_eq_self] using congrArg left hright
        exact htmp.symm
      exact ha0_out.2.2.1 this
  · rcases hnext_local with hleft | hself | hright
    · exfalso
      have : gc.moverAt a0 = right (right (right t)) := by
        have htmp : right (right (right t)) = gc.moverAt a0 := by
          simpa [ha1_r2, right_left_eq_self] using congrArg right hleft
        exact htmp.symm
      exact ha0_out.2.2.2.2.2 this
    · exfalso
      exact ha0_out.2.2.2.2.1 (by simpa [ha1_r2] using hself.symm)
    · exfalso
      have : gc.moverAt a0 = right t := by
        have htmp : right t = gc.moverAt a0 := by
          simpa [ha1_r2, left_right_eq_self] using congrArg left hright
        exact htmp.symm
      exact ha0_out.2.2.2.1 this
  · rcases hnext_local with hleft | hself | hright
    · have htmp : right (right (right (right t))) = gc.moverAt a0 := by
        simpa [ha1_r3, right_left_eq_self] using congrArg right hleft
      exact Or.inr htmp.symm
    · exfalso
      exact ha0_out.2.2.2.2.2 (by simpa [ha1_r3] using hself.symm)
    · exfalso
      have : gc.moverAt a0 = right (right t) := by
        have htmp : right (right t) = gc.moverAt a0 := by
          simpa [ha1_r3, left_right_eq_self] using congrArg left hright
        exact htmp.symm
      exact ha0_out.2.2.2.2.1 this

/-- If all steps from `cut` onward lie in the left-biased 6-neighborhood,
    then either every mover lies there globally, or the last prefix escape
    before `cut` is forced to be `left^4(t)` or `right^3(t)`. -/
private theorem all_left_six_or_prefix_bad_left4_or_right3
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (cut : Fin gc.configs.length)
    (htail :
      ∀ k : Fin gc.configs.length,
        cut.val ≤ k.val →
        gc.moverAt k = left (left (left t)) ∨
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t ∨
        gc.moverAt k = t ∨
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t)) :
    (∀ k : Fin gc.configs.length,
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t)) ∨
    ∃ j : Fin gc.configs.length,
      j.val < cut.val ∧
      (gc.moverAt j = left (left (left (left t))) ∨
        gc.moverAt j = right (right (right t))) := by
  by_cases hall :
      ∀ k : Fin gc.configs.length,
        gc.moverAt k = left (left (left t)) ∨
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t ∨
        gc.moverAt k = t ∨
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t)
  · exact Or.inl hall
  · right
    push_neg at hall
    have hbad_exists :
        ∃ k : Fin gc.configs.length,
          k.val < cut.val ∧
          gc.moverAt k ≠ left (left (left t)) ∧
          gc.moverAt k ≠ left (left t) ∧
          gc.moverAt k ≠ left t ∧
          gc.moverAt k ≠ t ∧
          gc.moverAt k ≠ right t ∧
          gc.moverAt k ≠ right (right t) := by
      obtain ⟨k0, hk0_bad⟩ := hall
      have hk0_lt : k0.val < cut.val := by
        by_contra hk0_ge
        push_neg at hk0_ge
        rcases htail k0 hk0_ge with hk | hk | hk | hk | hk | hk
        · exact hk0_bad.1 hk
        · exact hk0_bad.2.1 hk
        · exact hk0_bad.2.2.1 hk
        · exact hk0_bad.2.2.2.1 hk
        · exact hk0_bad.2.2.2.2.1 hk
        · exact hk0_bad.2.2.2.2.2 hk
      exact ⟨k0, hk0_lt, hk0_bad.1, hk0_bad.2.1, hk0_bad.2.2.1,
        hk0_bad.2.2.2.1, hk0_bad.2.2.2.2.1, hk0_bad.2.2.2.2.2⟩
    let badPrefix : Finset (Fin gc.configs.length) :=
      (Finset.univ : Finset (Fin gc.configs.length)).filter
        (fun k =>
          k.val < cut.val ∧
          gc.moverAt k ≠ left (left (left t)) ∧
          gc.moverAt k ≠ left (left t) ∧
          gc.moverAt k ≠ left t ∧
          gc.moverAt k ≠ t ∧
          gc.moverAt k ≠ right t ∧
          gc.moverAt k ≠ right (right t))
    obtain ⟨k0, hk0_lt, hk0_l3, hk0_l2, hk0_l1, hk0_t, hk0_r1, hk0_r2⟩ := hbad_exists
    have hk0_mem : k0 ∈ badPrefix := by
      refine Finset.mem_filter.mpr ?_
      exact ⟨Finset.mem_univ k0, hk0_lt, hk0_l3, hk0_l2, hk0_l1, hk0_t, hk0_r1, hk0_r2⟩
    have hne : badPrefix.Nonempty := ⟨k0, hk0_mem⟩
    obtain ⟨j, hj_mem, hj_max⟩ := Finset.exists_max_image badPrefix Fin.val hne
    have hj_lt : j.val < cut.val := by
      simp [badPrefix] at hj_mem
      exact hj_mem.1
    have hj_out :
        gc.moverAt j ≠ left (left (left t)) ∧
        gc.moverAt j ≠ left (left t) ∧
        gc.moverAt j ≠ left t ∧
        gc.moverAt j ≠ t ∧
        gc.moverAt j ≠ right t ∧
        gc.moverAt j ≠ right (right t) := by
      simp [badPrefix] at hj_mem
      exact hj_mem.2
    have hj1_lt_len : j.val + 1 < gc.configs.length := by
      exact lt_of_le_of_lt (Nat.succ_le_of_lt hj_lt) cut.isLt
    let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
    have hj1_eq_next : nextIndex gc.configs j = j1 := by
      apply Fin.ext
      simp [nextIndex, j1]
      exact Nat.mod_eq_of_lt hj1_lt_len
    have hj1_local :
        gc.moverAt j1 = left (left (left t)) ∨
        gc.moverAt j1 = left (left t) ∨
        gc.moverAt j1 = left t ∨
        gc.moverAt j1 = t ∨
        gc.moverAt j1 = right t ∨
        gc.moverAt j1 = right (right t) := by
      by_cases hj1_cut : cut.val ≤ j1.val
      · exact htail j1 hj1_cut
      · push_neg at hj1_cut
        by_contra hj1_bad
        have hj1_mem : j1 ∈ badPrefix := by
          refine Finset.mem_filter.mpr ?_
          refine ⟨Finset.mem_univ j1, ?_⟩
          push_neg at hj1_bad
          exact ⟨hj1_cut, hj1_bad⟩
        have hle := hj_max j1 hj1_mem
        have : j.val + 1 ≤ j.val := by
          simpa [j1] using hle
        omega
    exact ⟨j, hj_lt,
      outside_step_followed_by_left_six_forces_edge gc t j j1
        hj1_eq_next hj_out hj1_local⟩

/-- Strengthened left-biased prefix refinement: if a suffix lies in the
    left-biased 6-neighborhood, then either it already holds globally, or there
    is an earlier edge witness after which the left-six constraint holds
    continuously. -/
theorem all_left_six_or_prefix_bad_left4_or_right3_strong
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (cut : Fin gc.configs.length)
    (htail :
      ∀ k : Fin gc.configs.length,
        cut.val ≤ k.val →
        gc.moverAt k = left (left (left t)) ∨
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t ∨
        gc.moverAt k = t ∨
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t)) :
    (∀ k : Fin gc.configs.length,
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t)) ∨
    ∃ j : Fin gc.configs.length,
      j.val < cut.val ∧
      (gc.moverAt j = left (left (left (left t))) ∨
        gc.moverAt j = right (right (right t))) ∧
      (∀ k : Fin gc.configs.length,
        j.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t ∨
        gc.moverAt k = t ∨
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t)) := by
  by_cases hall :
      ∀ k : Fin gc.configs.length,
        gc.moverAt k = left (left (left t)) ∨
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t ∨
        gc.moverAt k = t ∨
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t)
  · exact Or.inl hall
  · right
    push_neg at hall
    let badPrefix : Finset (Fin gc.configs.length) :=
      (Finset.univ : Finset (Fin gc.configs.length)).filter
        (fun k =>
          k.val < cut.val ∧
          gc.moverAt k ≠ left (left (left t)) ∧
          gc.moverAt k ≠ left (left t) ∧
          gc.moverAt k ≠ left t ∧
          gc.moverAt k ≠ t ∧
          gc.moverAt k ≠ right t ∧
          gc.moverAt k ≠ right (right t))
    have hbad_exists :
        ∃ k : Fin gc.configs.length, k ∈ badPrefix := by
      obtain ⟨k0, hk0_bad⟩ := hall
      have hk0_lt : k0.val < cut.val := by
        by_contra hk0_ge
        push_neg at hk0_ge
        rcases htail k0 hk0_ge with hk | hk | hk | hk | hk | hk
        · exact hk0_bad.1 hk
        · exact hk0_bad.2.1 hk
        · exact hk0_bad.2.2.1 hk
        · exact hk0_bad.2.2.2.1 hk
        · exact hk0_bad.2.2.2.2.1 hk
        · exact hk0_bad.2.2.2.2.2 hk
      refine ⟨k0, Finset.mem_filter.mpr ?_⟩
      exact ⟨Finset.mem_univ k0, hk0_lt, hk0_bad.1, hk0_bad.2.1, hk0_bad.2.2.1,
        hk0_bad.2.2.2.1, hk0_bad.2.2.2.2.1, hk0_bad.2.2.2.2.2⟩
    rcases hbad_exists with ⟨k0, hk0_mem⟩
    obtain ⟨j, hj_mem, hj_max⟩ := Finset.exists_max_image badPrefix Fin.val ⟨k0, hk0_mem⟩
    have hj_lt : j.val < cut.val := by
      simp [badPrefix] at hj_mem
      exact hj_mem.1
    have hj_out :
        gc.moverAt j ≠ left (left (left t)) ∧
        gc.moverAt j ≠ left (left t) ∧
        gc.moverAt j ≠ left t ∧
        gc.moverAt j ≠ t ∧
        gc.moverAt j ≠ right t ∧
        gc.moverAt j ≠ right (right t) := by
      simp [badPrefix] at hj_mem
      exact hj_mem.2
    have hj1_lt_len : j.val + 1 < gc.configs.length := by
      exact lt_of_le_of_lt (Nat.succ_le_of_lt hj_lt) cut.isLt
    let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
    have hj1_eq_next : nextIndex gc.configs j = j1 := by
      apply Fin.ext
      simp [nextIndex, j1]
      exact Nat.mod_eq_of_lt hj1_lt_len
    have hj1_local :
        gc.moverAt j1 = left (left (left t)) ∨
        gc.moverAt j1 = left (left t) ∨
        gc.moverAt j1 = left t ∨
        gc.moverAt j1 = t ∨
        gc.moverAt j1 = right t ∨
        gc.moverAt j1 = right (right t) := by
      by_cases hj1_cut : cut.val ≤ j1.val
      · exact htail j1 hj1_cut
      · push_neg at hj1_cut
        by_cases hj1_local :
            gc.moverAt j1 = left (left (left t)) ∨
            gc.moverAt j1 = left (left t) ∨
            gc.moverAt j1 = left t ∨
            gc.moverAt j1 = t ∨
            gc.moverAt j1 = right t ∨
            gc.moverAt j1 = right (right t)
        · exact hj1_local
        · push_neg at hj1_local
          have hj1_mem : j1 ∈ badPrefix := by
            refine Finset.mem_filter.mpr ?_
            exact ⟨Finset.mem_univ j1, hj1_cut, hj1_local.1, hj1_local.2.1,
              hj1_local.2.2.1, hj1_local.2.2.2.1, hj1_local.2.2.2.2.1,
              hj1_local.2.2.2.2.2⟩
          have hle := hj_max j1 hj1_mem
          have hsucc : j.val + 1 ≤ j.val := by
            simpa [j1] using hle
          exact False.elim (Nat.not_succ_le_self j.val hsucc)
    have hj_edge :
        gc.moverAt j = left (left (left (left t))) ∨
        gc.moverAt j = right (right (right t)) := by
      exact outside_step_followed_by_left_six_forces_edge gc t j j1
        hj1_eq_next hj_out hj1_local
    have hj_tail :
        ∀ k : Fin gc.configs.length,
          j.val < k.val →
          gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) := by
      intro k hjk
      by_cases hk_cut : cut.val ≤ k.val
      · exact htail k hk_cut
      · have hk_lt_cut : k.val < cut.val := by omega
        by_cases hk_local :
            gc.moverAt k = left (left (left t)) ∨
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t)
        · exact hk_local
        · push_neg at hk_local
          have hk_mem : k ∈ badPrefix := by
            refine Finset.mem_filter.mpr ?_
            exact ⟨Finset.mem_univ k, hk_lt_cut, hk_local.1, hk_local.2.1,
              hk_local.2.2.1, hk_local.2.2.2.1, hk_local.2.2.2.2.1,
              hk_local.2.2.2.2.2⟩
          have hle := hj_max k hk_mem
          have : k.val ≤ j.val := by simpa using hle
          omega
    exact ⟨j, hj_lt, hj_edge, hj_tail⟩

/-- Symmetric right-biased prefix-refinement lemma. -/
private theorem all_right_six_or_prefix_bad_left3_or_right4
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (cut : Fin gc.configs.length)
    (htail :
      ∀ k : Fin gc.configs.length,
        cut.val ≤ k.val →
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t ∨
        gc.moverAt k = t ∨
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t) ∨
        gc.moverAt k = right (right (right t))) :
    (∀ k : Fin gc.configs.length,
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t))) ∨
    ∃ j : Fin gc.configs.length,
      j.val < cut.val ∧
      (gc.moverAt j = left (left (left t)) ∨
        gc.moverAt j = right (right (right (right t)))) := by
  by_cases hall :
      ∀ k : Fin gc.configs.length,
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t ∨
        gc.moverAt k = t ∨
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t) ∨
        gc.moverAt k = right (right (right t))
  · exact Or.inl hall
  · right
    push_neg at hall
    have hbad_exists :
        ∃ k : Fin gc.configs.length,
          k.val < cut.val ∧
          gc.moverAt k ≠ left (left t) ∧
          gc.moverAt k ≠ left t ∧
          gc.moverAt k ≠ t ∧
          gc.moverAt k ≠ right t ∧
          gc.moverAt k ≠ right (right t) ∧
          gc.moverAt k ≠ right (right (right t)) := by
      obtain ⟨k0, hk0_bad⟩ := hall
      have hk0_lt : k0.val < cut.val := by
        by_contra hk0_ge
        push_neg at hk0_ge
        rcases htail k0 hk0_ge with hk | hk | hk | hk | hk | hk
        · exact hk0_bad.1 hk
        · exact hk0_bad.2.1 hk
        · exact hk0_bad.2.2.1 hk
        · exact hk0_bad.2.2.2.1 hk
        · exact hk0_bad.2.2.2.2.1 hk
        · exact hk0_bad.2.2.2.2.2 hk
      exact ⟨k0, hk0_lt, hk0_bad.1, hk0_bad.2.1, hk0_bad.2.2.1,
        hk0_bad.2.2.2.1, hk0_bad.2.2.2.2.1, hk0_bad.2.2.2.2.2⟩
    let badPrefix : Finset (Fin gc.configs.length) :=
      (Finset.univ : Finset (Fin gc.configs.length)).filter
        (fun k =>
          k.val < cut.val ∧
          gc.moverAt k ≠ left (left t) ∧
          gc.moverAt k ≠ left t ∧
          gc.moverAt k ≠ t ∧
          gc.moverAt k ≠ right t ∧
          gc.moverAt k ≠ right (right t) ∧
          gc.moverAt k ≠ right (right (right t)))
    obtain ⟨k0, hk0_lt, hk0_l2, hk0_l1, hk0_t, hk0_r1, hk0_r2, hk0_r3⟩ := hbad_exists
    have hk0_mem : k0 ∈ badPrefix := by
      refine Finset.mem_filter.mpr ?_
      exact ⟨Finset.mem_univ k0, hk0_lt, hk0_l2, hk0_l1, hk0_t, hk0_r1, hk0_r2, hk0_r3⟩
    have hne : badPrefix.Nonempty := ⟨k0, hk0_mem⟩
    obtain ⟨j, hj_mem, hj_max⟩ := Finset.exists_max_image badPrefix Fin.val hne
    have hj_lt : j.val < cut.val := by
      simp [badPrefix] at hj_mem
      exact hj_mem.1
    have hj_out :
        gc.moverAt j ≠ left (left t) ∧
        gc.moverAt j ≠ left t ∧
        gc.moverAt j ≠ t ∧
        gc.moverAt j ≠ right t ∧
        gc.moverAt j ≠ right (right t) ∧
        gc.moverAt j ≠ right (right (right t)) := by
      simp [badPrefix] at hj_mem
      exact hj_mem.2
    have hj1_lt_len : j.val + 1 < gc.configs.length := by
      exact lt_of_le_of_lt (Nat.succ_le_of_lt hj_lt) cut.isLt
    let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
    have hj1_eq_next : nextIndex gc.configs j = j1 := by
      apply Fin.ext
      simp [nextIndex, j1]
      exact Nat.mod_eq_of_lt hj1_lt_len
    have hj1_local :
        gc.moverAt j1 = left (left t) ∨
        gc.moverAt j1 = left t ∨
        gc.moverAt j1 = t ∨
        gc.moverAt j1 = right t ∨
        gc.moverAt j1 = right (right t) ∨
        gc.moverAt j1 = right (right (right t)) := by
      by_cases hj1_cut : cut.val ≤ j1.val
      · exact htail j1 hj1_cut
      · push_neg at hj1_cut
        by_contra hj1_bad
        have hj1_mem : j1 ∈ badPrefix := by
          refine Finset.mem_filter.mpr ?_
          refine ⟨Finset.mem_univ j1, ?_⟩
          push_neg at hj1_bad
          exact ⟨hj1_cut, hj1_bad⟩
        have hle := hj_max j1 hj1_mem
        have : j.val + 1 ≤ j.val := by
          simpa [j1] using hle
        omega
    exact ⟨j, hj_lt,
      outside_step_followed_by_right_six_forces_edge gc t j j1
        hj1_eq_next hj_out hj1_local⟩

/-- Strengthened right-biased prefix refinement: if a suffix lies in the
    right-biased 6-neighborhood, then either it already holds globally, or there
    is an earlier edge witness after which the right-six constraint holds
    continuously. -/
theorem all_right_six_or_prefix_bad_left3_or_right4_strong
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (cut : Fin gc.configs.length)
    (htail :
      ∀ k : Fin gc.configs.length,
        cut.val ≤ k.val →
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t ∨
        gc.moverAt k = t ∨
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t) ∨
        gc.moverAt k = right (right (right t))) :
    (∀ k : Fin gc.configs.length,
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t))) ∨
    ∃ j : Fin gc.configs.length,
      j.val < cut.val ∧
      (gc.moverAt j = left (left (left t)) ∨
        gc.moverAt j = right (right (right (right t)))) ∧
      (∀ k : Fin gc.configs.length,
        j.val < k.val →
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t ∨
        gc.moverAt k = t ∨
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t) ∨
        gc.moverAt k = right (right (right t))) := by
  by_cases hall :
      ∀ k : Fin gc.configs.length,
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t ∨
        gc.moverAt k = t ∨
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t) ∨
        gc.moverAt k = right (right (right t))
  · exact Or.inl hall
  · right
    push_neg at hall
    let badPrefix : Finset (Fin gc.configs.length) :=
      (Finset.univ : Finset (Fin gc.configs.length)).filter
        (fun k =>
          k.val < cut.val ∧
          gc.moverAt k ≠ left (left t) ∧
          gc.moverAt k ≠ left t ∧
          gc.moverAt k ≠ t ∧
          gc.moverAt k ≠ right t ∧
          gc.moverAt k ≠ right (right t) ∧
          gc.moverAt k ≠ right (right (right t)))
    have hbad_exists :
        ∃ k : Fin gc.configs.length, k ∈ badPrefix := by
      obtain ⟨k0, hk0_bad⟩ := hall
      have hk0_lt : k0.val < cut.val := by
        by_contra hk0_ge
        push_neg at hk0_ge
        rcases htail k0 hk0_ge with hk | hk | hk | hk | hk | hk
        · exact hk0_bad.1 hk
        · exact hk0_bad.2.1 hk
        · exact hk0_bad.2.2.1 hk
        · exact hk0_bad.2.2.2.1 hk
        · exact hk0_bad.2.2.2.2.1 hk
        · exact hk0_bad.2.2.2.2.2 hk
      refine ⟨k0, Finset.mem_filter.mpr ?_⟩
      exact ⟨Finset.mem_univ k0, hk0_lt, hk0_bad.1, hk0_bad.2.1, hk0_bad.2.2.1,
        hk0_bad.2.2.2.1, hk0_bad.2.2.2.2.1, hk0_bad.2.2.2.2.2⟩
    rcases hbad_exists with ⟨k0, hk0_mem⟩
    obtain ⟨j, hj_mem, hj_max⟩ := Finset.exists_max_image badPrefix Fin.val ⟨k0, hk0_mem⟩
    have hj_lt : j.val < cut.val := by
      simp [badPrefix] at hj_mem
      exact hj_mem.1
    have hj_out :
        gc.moverAt j ≠ left (left t) ∧
        gc.moverAt j ≠ left t ∧
        gc.moverAt j ≠ t ∧
        gc.moverAt j ≠ right t ∧
        gc.moverAt j ≠ right (right t) ∧
        gc.moverAt j ≠ right (right (right t)) := by
      simp [badPrefix] at hj_mem
      exact hj_mem.2
    have hj1_lt_len : j.val + 1 < gc.configs.length := by
      exact lt_of_le_of_lt (Nat.succ_le_of_lt hj_lt) cut.isLt
    let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
    have hj1_eq_next : nextIndex gc.configs j = j1 := by
      apply Fin.ext
      simp [nextIndex, j1]
      exact Nat.mod_eq_of_lt hj1_lt_len
    have hj1_local :
        gc.moverAt j1 = left (left t) ∨
        gc.moverAt j1 = left t ∨
        gc.moverAt j1 = t ∨
        gc.moverAt j1 = right t ∨
        gc.moverAt j1 = right (right t) ∨
        gc.moverAt j1 = right (right (right t)) := by
      by_cases hj1_cut : cut.val ≤ j1.val
      · exact htail j1 hj1_cut
      · push_neg at hj1_cut
        by_cases hj1_local :
            gc.moverAt j1 = left (left t) ∨
            gc.moverAt j1 = left t ∨
            gc.moverAt j1 = t ∨
            gc.moverAt j1 = right t ∨
            gc.moverAt j1 = right (right t) ∨
            gc.moverAt j1 = right (right (right t))
        · exact hj1_local
        · push_neg at hj1_local
          have hj1_mem : j1 ∈ badPrefix := by
            refine Finset.mem_filter.mpr ?_
            exact ⟨Finset.mem_univ j1, hj1_cut, hj1_local.1, hj1_local.2.1,
              hj1_local.2.2.1, hj1_local.2.2.2.1, hj1_local.2.2.2.2.1,
              hj1_local.2.2.2.2.2⟩
          have hle := hj_max j1 hj1_mem
          have hsucc : j.val + 1 ≤ j.val := by
            simpa [j1] using hle
          exact False.elim (Nat.not_succ_le_self j.val hsucc)
    have hj_edge :
        gc.moverAt j = left (left (left t)) ∨
        gc.moverAt j = right (right (right (right t))) := by
      exact outside_step_followed_by_right_six_forces_edge gc t j j1
        hj1_eq_next hj_out hj1_local
    have hj_tail :
        ∀ k : Fin gc.configs.length,
          j.val < k.val →
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t)) := by
      intro k hjk
      by_cases hk_cut : cut.val ≤ k.val
      · exact htail k hk_cut
      · have hk_lt_cut : k.val < cut.val := by omega
        by_cases hk_local :
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t) ∨
            gc.moverAt k = right (right (right t))
        · exact hk_local
        · push_neg at hk_local
          have hk_mem : k ∈ badPrefix := by
            refine Finset.mem_filter.mpr ?_
            exact ⟨Finset.mem_univ k, hk_lt_cut, hk_local.1, hk_local.2.1,
              hk_local.2.2.1, hk_local.2.2.2.1, hk_local.2.2.2.2.1,
              hk_local.2.2.2.2.2⟩
          have hle := hj_max k hk_mem
          have : k.val ≤ j.val := by simpa using hle
          omega
    exact ⟨j, hj_lt, hj_edge, hj_tail⟩

/-! ### Firing support reduction -/

/-- The firing support: the set of processors that fire at least once. -/
private noncomputable def firingSupport (gc : GoodCycle sys) : Finset (Fin sys.rs.n) :=
  Finset.filter (fun p => gc.fireCount p > 0) Finset.univ

/-- The zero set: processors that never fire. -/
noncomputable def zeroSet (gc : GoodCycle sys) : Finset (Fin sys.rs.n) :=
  Finset.filter (fun p => gc.fireCount p = 0) Finset.univ

/-- Firing support and zero set partition the ring. -/
private theorem firingSupport_union_zeroSet (gc : GoodCycle sys) :
    firingSupport gc ∪ zeroSet gc = Finset.univ := by
  ext p; simp [firingSupport, zeroSet]; omega

private theorem firingSupport_disjoint_zeroSet (gc : GoodCycle sys) :
    Disjoint (firingSupport gc) (zeroSet gc) := by
  simp only [firingSupport, zeroSet]
  exact Finset.disjoint_filter.mpr (fun p _ h1 h2 => by omega)

private theorem firingSupport_card_add_zeroSet (gc : GoodCycle sys) :
    (firingSupport gc).card + (zeroSet gc).card = sys.rs.n := by
  have h1 := Finset.card_union_of_disjoint (firingSupport_disjoint_zeroSet gc)
  rw [firingSupport_union_zeroSet] at h1
  rw [Finset.card_fin] at h1; omega

/-- hno_safe implies every processor is within distance 1 of a firing processor:
    the firing support dominates the ring. -/
private theorem firingSupport_dominates (gc : GoodCycle sys)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (q : Fin sys.rs.n) :
    gc.fireCount q > 0 ∨ gc.fireCount (left q) > 0 ∨ gc.fireCount (right q) > 0 := by
  obtain ⟨k, hvisit⟩ := hno_safe_visit gc hno_safe q
  rcases hvisit with hmov | hmov | hmov
  · left; exact fireCount_pos_of_moverAt_eq gc q k hmov
  · right; left; exact fireCount_pos_of_moverAt_eq gc (left q) k hmov
  · right; right; exact fireCount_pos_of_moverAt_eq gc (right q) k hmov

/-- If q doesn't fire, then one of its neighbors fires (from domination). -/
private theorem neighbor_fires_of_zeroFC (gc : GoodCycle sys)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (q : Fin sys.rs.n) (hq : gc.fireCount q = 0) :
    gc.fireCount (left q) > 0 ∨ gc.fireCount (right q) > 0 := by
  have hdom := firingSupport_dominates gc hno_safe q
  rcases hdom with h | h | h
  · omega
  · exact Or.inl h
  · exact Or.inr h

/-- Two consecutive non-firing processors cannot have a non-firing right neighbor:
    if fc(i) = 0 and fc(right i) = 0, then fc(right(right i)) > 0.
    Proof: domination at right(i) forces left(right i) = i or right(right i) to fire.
    Since fc(i) = 0, it must be right(right i). -/
private theorem no_three_consecutive_zeroFC (gc : GoodCycle sys)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (i : Fin sys.rs.n) (hfc_i : gc.fireCount i = 0)
    (hfc_ri : gc.fireCount (right i) = 0) :
    gc.fireCount (right (right i)) > 0 := by
  -- If fc(right(right i)) = 0 too, then right(i) is safe → contradiction
  by_contra hfc_rri
  push_neg at hfc_rri
  have hfc_rri_eq : gc.fireCount (right (right i)) = 0 := by omega
  apply hno_safe
  refine ⟨right i, fun k => ⟨?_, ?_, ?_⟩⟩
  · -- moverAt k ≠ right i
    intro hmov; have := fireCount_pos_of_moverAt_eq gc (right i) k hmov; omega
  · -- moverAt k ≠ left(right i) = i
    rw [left_right_eq_self]
    intro hmov; have := fireCount_pos_of_moverAt_eq gc i k hmov; omega
  · -- moverAt k ≠ right(right i)
    intro hmov; have := fireCount_pos_of_moverAt_eq gc (right (right i)) k hmov; omega

/-- **Mover walk stays in firing support.**
    Every moverAt value has positive fire count (trivially: moverAt(k) = p
    means p fires at step k, so fc(p) > 0). -/
private theorem moverAt_mem_firingSupport (gc : GoodCycle sys)
    (k : Fin gc.configs.length) :
    gc.moverAt k ∈ firingSupport gc := by
  simp [firingSupport]
  exact fireCount_pos_of_moverAt_eq gc (gc.moverAt k) k rfl

/-- **Discrete IVT for natural-valued walks.**
    If a sequence f : ℕ → ℕ satisfies f(k+1) ≤ f(k) + 1 for k < m,
    and f(0) ≤ v ≤ f(m), then ∃ k ≤ m with f(k) = v.

    Note: we only need the "step up by at most 1" direction, since we
    apply this to the maximum CW displacement of the walk. -/
private theorem discrete_ivt : ∀ (m : Nat) (f : Nat → Nat),
    (∀ k, k < m → f (k + 1) ≤ f k + 1) →
    (∀ k, k < m → f k ≤ f (k + 1) + 1) →
    ∀ (v : Nat), f 0 ≤ v → v ≤ f m →
    ∃ k, k ≤ m ∧ f k = v := by
  intro m
  induction m with
  | zero => intro f _ _ v hlo hhi; exact ⟨0, le_rfl, by omega⟩
  | succ m ih =>
    intro f hup hdn v hlo hhi
    by_cases hfm_ge : v ≤ f m
    · obtain ⟨k, hk, hfk⟩ := ih f (fun k hk => hup k (by omega))
        (fun k hk => hdn k (by omega)) v hlo hfm_ge
      exact ⟨k, by omega, hfk⟩
    · push_neg at hfm_ge
      have h1 := hup m (by omega)
      exact ⟨m + 1, le_rfl, by omega⟩

/-- The walk never visits a proc with fc = 0. -/
private theorem moverAt_ne_of_fc_zero (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hfc : gc.fireCount p = 0)
    (k : Fin gc.configs.length) : gc.moverAt k ≠ p := by
  intro hmov; exact absurd (fireCount_pos_of_moverAt_eq gc p k hmov) (by omega)

/-! #### CW displacement and walk connectivity -/

/-- CW distance from `right p` to `q`: d(q) = (q + n - right(p)) % n. -/
private def cwShift {n : Nat} (p q : Fin n) : Nat :=
  (q.val + n - (right p).val) % n

/-- cwShift p (right p) = 0. -/
private theorem cwShift_right_self {n : Nat} (hn : n ≥ 4) (p : Fin n) :
    cwShift p (right p) = 0 := by
  simp [cwShift, right_val, Nat.sub_self, Nat.mod_self]

/-- cwShift p p = n - 1. -/
private theorem cwShift_self {n : Nat} (hn : n ≥ 4) (p : Fin n) :
    cwShift p p = n - 1 := by
  unfold cwShift
  simp only [right_val]
  by_cases h : p.val + 1 < n
  · rw [Nat.mod_eq_of_lt h, show p.val + n - (p.val + 1) = n - 1 by omega,
      Nat.mod_eq_of_lt (by omega)]
  · have : p.val + 1 = n := by omega
    rw [this, Nat.mod_self, show p.val + n - 0 = p.val + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt p.isLt]; omega

/-- cwShift < n. -/
private theorem cwShift_lt {n : Nat} (hn : n ≥ 1) (p q : Fin n) :
    cwShift p q < n := Nat.mod_lt _ (by omega)

/-- cwShift = n - 1 iff q = p. -/
private theorem cwShift_eq_pred_iff {n : Nat} (hn : n ≥ 4) (p q : Fin n) :
    cwShift p q = n - 1 ↔ q = p := by
  constructor
  · intro heq
    unfold cwShift at heq
    have hq := q.isLt; have hp := p.isLt
    have hrp := (right p).isLt
    have hrp_val : (right p).val = (p.val + 1) % n := right_val p
    -- In both cases, (right p).val = (p+1)%n. Substitute and simplify.
    have hrp_eq : (right p).val = if p.val + 1 < n then p.val + 1 else 0 := by
      rw [hrp_val]; split_ifs with hw
      · exact Nat.mod_eq_of_lt hw
      · exact show (p.val + 1) % n = 0 by rw [show p.val + 1 = n by omega]; exact Nat.mod_self n
    rcases Nat.lt_or_ge (q.val + n - (right p).val) n with h | h
    · rw [Nat.mod_eq_of_lt h] at heq
      split_ifs at hrp_eq with hw
      · rw [hrp_eq] at heq; exact Fin.ext (by omega)
      · rw [hrp_eq] at heq; omega
    · rw [show q.val + n - (right p).val = (q.val + n - (right p).val - n) + n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at heq
      split_ifs at hrp_eq with hw
      · rw [hrp_eq] at heq; exact Fin.ext (by omega)
      · rw [hrp_eq] at heq; exact Fin.ext (by omega)
  · intro h; rw [h]; exact cwShift_self hn p

/-- cwShift = 0 iff q = right p. -/
private theorem cwShift_eq_zero_iff {n : Nat} (hn : n ≥ 4) (p q : Fin n) :
    cwShift p q = 0 ↔ q = right p := by
  constructor
  · intro heq
    unfold cwShift at heq
    have hq := q.isLt; have hrp := (right p).isLt
    rcases Nat.lt_or_ge (q.val + n - (right p).val) n with h | h
    · rw [Nat.mod_eq_of_lt h] at heq; exact Fin.ext (by omega)
    · rw [show q.val + n - (right p).val = (q.val + n - (right p).val - n) + n by omega,
        Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)] at heq
      exact Fin.ext (by omega)
  · intro h; rw [h]; exact cwShift_right_self hn p

/-- Right step: if cwShift < n-1, then cwShift(right q) = cwShift(q) + 1. -/
private theorem cwShift_right_step {n : Nat} (hn : n ≥ 4) (p q : Fin n)
    (hlt : cwShift p q < n - 1) :
    cwShift p (right q) = cwShift p q + 1 := by
  -- cwShift p (right q) = ((q+1)%n + n - rp) % n
  -- cwShift p q = (q + n - rp) % n = d, where d < n - 1
  -- We need: ((q+1)%n + n - rp) % n = d + 1
  -- Since d < n - 1, d + 1 < n. The proof is modular arithmetic case analysis.
  have hq := q.isLt; have hrp := (right p).isLt
  have hd_lt : cwShift p q < n := Nat.mod_lt _ (by omega)
  -- Expand cwShift
  show ((right q).val + n - (right p).val) % n = cwShift p q + 1
  have hcw : (q.val + n - (right p).val) % n = cwShift p q := rfl
  rw [right_val]
  by_cases hq1 : q.val + 1 < n
  · rw [Nat.mod_eq_of_lt hq1]
    -- (q+1 + n - rp) % n = ((q + n - rp) + 1) % n
    -- Since (q + n - rp) % n = d and d + 1 < n: result = d + 1
    rcases Nat.lt_or_ge (q.val + n - (right p).val) n with h | h
    · -- q + n - rp < n: mod is identity
      rw [Nat.mod_eq_of_lt h] at hcw
      rw [show q.val + 1 + n - (right p).val = cwShift p q + 1 by omega,
        Nat.mod_eq_of_lt (by omega)]
    · -- q + n - rp ≥ n: mod subtracts n
      have hlt2 : q.val + n - (right p).val < 2 * n := by omega
      rw [show q.val + n - (right p).val = (q.val + n - (right p).val - n) + n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hcw
      -- cwShift p q = q - rp. q + 1 + n - rp = cwShift + 1 + n
      rw [show q.val + 1 + n - (right p).val = cwShift p q + 1 + n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · -- q + 1 = n: right q = 0
    have hqn : q.val + 1 = n := by omega
    rw [hqn, Nat.mod_self]
    -- (0 + n - rp) % n
    rcases Nat.lt_or_ge (q.val + n - (right p).val) n with h | h
    · rw [Nat.mod_eq_of_lt h] at hcw
      -- cwShift = q + n - rp. 0 + n - rp = n - rp.
      -- cwShift + 1 = q + n - rp + 1 = (n - 1) + n - rp + 1 = 2n - rp.
      -- n - rp = cwShift + 1 - n + n... hmm.
      -- Actually: cwShift = q + n - rp = (n-1) + n - rp (since q = n-1).
      -- But cwShift < n, so (n-1) + n - rp < n → rp > n - 1 → rp = n - 1... no rp < n.
      -- Actually (n-1) + n - rp = 2n - 1 - rp. For this < n: rp > n - 1, so rp ≥ n. But rp < n.
      -- So this case can't happen (h says q + n - rp < n, but q = n-1, so n-1+n-rp < n, 2n-1-rp < n, rp > n-1, rp ≥ n, contradiction).
      omega
    · have hlt2 : q.val + n - (right p).val < 2 * n := by omega
      rw [show q.val + n - (right p).val = (q.val + n - (right p).val - n) + n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hcw
      rw [show 0 + n - (right p).val = cwShift p q + 1 by omega,
        Nat.mod_eq_of_lt (by omega)]

/-- Left step: if cwShift > 0, then cwShift(left q) = cwShift(q) - 1. -/
private theorem cwShift_left_step {n : Nat} (hn : n ≥ 4) (p q : Fin n)
    (hpos : 0 < cwShift p q) :
    cwShift p (left q) = cwShift p q - 1 := by
  -- Symmetric to cwShift_right_step: left-stepping decrements CW distance by 1.
  -- cwShift p (left q) = ((q+n-1)%n + n - rp) % n = (q + 2n - 1 - rp) % n
  -- = ((q + n - rp) - 1) % n = (cwShift p q - 1) % n = cwShift p q - 1
  -- (since cwShift p q ≥ 1, so cwShift p q - 1 < n).
  have hq := q.isLt; have hrp := (right p).isLt
  have hd_lt : cwShift p q < n := Nat.mod_lt _ (by omega)
  have hcw : (q.val + n - (right p).val) % n = cwShift p q := rfl
  show ((left q).val + n - (right p).val) % n = cwShift p q - 1
  rw [left_val]
  by_cases hq0 : q.val = 0
  · -- q = 0: left q = n - 1
    rw [hq0]; simp only [Nat.zero_add]
    rw [Nat.mod_eq_of_lt (show n - 1 < n by omega)]
    rw [hq0] at hcw
    -- cw = (0 + n - rp) % n = (n - rp) % n
    -- Since rp < n: n - rp ∈ [1, n]. If rp = 0: n - 0 = n, mod = 0, contradicts hpos.
    -- If rp > 0: n - rp < n, mod = n - rp. So cw = n - rp.
    by_cases hrp0 : (right p).val = 0
    · rw [hrp0] at hcw; simp at hcw; omega
    · rw [show 0 + n - (right p).val = n - (right p).val by omega] at hcw
      rw [Nat.mod_eq_of_lt (show n - (right p).val < n by omega)] at hcw
      -- cw = n - rp. Goal: (n - 1 + n - rp) % n = cw - 1 = n - rp - 1.
      rw [show n - 1 + n - (right p).val = (cwShift p q - 1) + n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · -- q > 0: left q = q - 1
    have hq_pos : 0 < q.val := by omega
    rw [show q.val + n - 1 = (q.val - 1) + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (show q.val - 1 < n by omega)]
    -- Goal: (q - 1 + n - rp) % n = cw - 1
    rcases Nat.lt_or_ge (q.val + n - (right p).val) n with h | h
    · -- q + n - rp < n: cw = q + n - rp
      rw [Nat.mod_eq_of_lt h] at hcw
      -- q - 1 + n - rp = cw - 1 (since cw = q + n - rp ≥ 1)
      rw [show q.val - 1 + n - (right p).val = cwShift p q - 1 by omega,
        Nat.mod_eq_of_lt (by omega)]
    · -- q + n - rp ≥ n: cw = q + n - rp - n = q - rp
      rw [show q.val + n - (right p).val = (q.val + n - (right p).val - n) + n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hcw
      -- cw = q - rp ≥ 1, so q ≥ rp + 1, q - 1 ≥ rp.
      -- q - 1 + n - rp = (q - rp - 1) + n = (cw - 1) + n
      rw [show q.val - 1 + n - (right p).val = (cwShift p q - 1) + n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- cwShift is injective on Fin n. -/
private theorem cwShift_injective {n : Nat} (hn : n ≥ 4) (p : Fin n)
    {q₁ q₂ : Fin n} (heq : cwShift p q₁ = cwShift p q₂) : q₁ = q₂ := by
  unfold cwShift at heq
  have hq₁ := q₁.isLt; have hq₂ := q₂.isLt; have hrp := (right p).isLt
  rcases Nat.lt_or_ge (q₁.val + n - (right p).val) n with h₁ | h₁ <;>
  rcases Nat.lt_or_ge (q₂.val + n - (right p).val) n with h₂ | h₂
  · rw [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at heq
    exact Fin.ext (by omega)
  · rw [Nat.mod_eq_of_lt h₁,
      show q₂.val + n - (right p).val = (q₂.val + n - (right p).val - n) + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at heq
    exact Fin.ext (by omega)
  · rw [show q₁.val + n - (right p).val = (q₁.val + n - (right p).val - n) + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h₂] at heq
    exact Fin.ext (by omega)
  · rw [show q₁.val + n - (right p).val = (q₁.val + n - (right p).val - n) + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
      show q₂.val + n - (right p).val = (q₂.val + n - (right p).val - n) + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at heq
    exact Fin.ext (by omega)

/-- Exact CW displacement of `left p` from `right p`. -/
private theorem cwShift_left_self {n : Nat} (hn : n ≥ 5) (p : Fin n) :
    cwShift p (left p) = n - 2 := by
  have hN4 : n ≥ 4 := by omega
  have hpos : 0 < cwShift p p := by
    rw [cwShift_self hN4 p]
    omega
  rw [cwShift_left_step hN4 p p hpos, cwShift_self hN4 p]
  omega

/-- Exact CW displacement of `left (left p)` from `right p`. -/
private theorem cwShift_left2_self {n : Nat} (hn : n ≥ 6) (p : Fin n) :
    cwShift p (left (left p)) = n - 3 := by
  have hN5 : n ≥ 5 := by omega
  have hpos : 0 < cwShift p (left p) := by
    rw [cwShift_left_self hN5 p]
    omega
  rw [cwShift_left_step (by omega) p (left p) hpos, cwShift_left_self hN5 p]
  omega

/-- Exact CW displacement of `left (left (left p))` from `right p`. -/
private theorem cwShift_left3_self {n : Nat} (hn : n ≥ 7) (p : Fin n) :
    cwShift p (left (left (left p))) = n - 4 := by
  have hN6 : n ≥ 6 := by omega
  have hpos : 0 < cwShift p (left (left p)) := by
    rw [cwShift_left2_self hN6 p]
    omega
  rw [cwShift_left_step (by omega) p (left (left p)) hpos, cwShift_left2_self hN6 p]
  omega

/-- Exact CW displacement of `left (left (left (left p)))` from `right p`. -/
private theorem cwShift_left4_self {n : Nat} (hn : n ≥ 7) (p : Fin n) :
    cwShift p (left (left (left (left p)))) = n - 5 := by
  have hN7 : n ≥ 7 := by omega
  have hpos : 0 < cwShift p (left (left (left p))) := by
    rw [cwShift_left3_self hN7 p]
    omega
  rw [cwShift_left_step (by omega) p (left (left (left p))) hpos,
    cwShift_left3_self hN7 p]
  omega

/-- Exact CW displacement of `right (right p)` from `right p`. -/
private theorem cwShift_right2_self {n : Nat} (hn : n ≥ 4) (p : Fin n) :
    cwShift p (right (right p)) = 1 := by
  have hlt : cwShift p (right p) < n - 1 := by
    rw [cwShift_right_self hn p]
    omega
  rw [cwShift_right_step hn p (right p) hlt, cwShift_right_self hn p]

/-- Exact CW displacement of `right (right (right p))` from `right p`. -/
private theorem cwShift_right3_self {n : Nat} (hn : n ≥ 5) (p : Fin n) :
    cwShift p (right (right (right p))) = 2 := by
  have hN4 : n ≥ 4 := by omega
  have hlt : cwShift p (right (right p)) < n - 1 := by
    rw [cwShift_right2_self hN4 p]
    omega
  rw [cwShift_right_step hN4 p (right (right p)) hlt, cwShift_right2_self hN4 p]

/-- Exact CW displacement of `right (right (right (right p)))` from `right p`. -/
private theorem cwShift_right4_self {n : Nat} (hn : n ≥ 6) (p : Fin n) :
    cwShift p (right (right (right (right p)))) = 3 := by
  have hN5 : n ≥ 5 := by omega
  have hlt : cwShift p (right (right (right p))) < n - 1 := by
    rw [cwShift_right3_self hN5 p]
    omega
  rw [cwShift_right_step (by omega) p (right (right (right p))) hlt,
    cwShift_right3_self hN5 p]

/-- `left^3(t)` is not in the pivot's local 5-neighborhood when `n ≥ 7`. -/
theorem left3_not_local5 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    ¬(left (left (left t)) = left (left t) ∨
      left (left (left t)) = left t ∨
      left (left (left t)) = right t ∨
      left (left (left t)) = right (right t)) := by
  intro h
  rcases h with h | h | h | h
  · have := congrArg (cwShift t) h
    rw [cwShift_left3_self (by omega) t, cwShift_left2_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_left3_self (by omega) t, cwShift_left_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_left3_self (by omega) t, cwShift_right_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_left3_self (by omega) t, cwShift_right2_self (by omega) t] at this
    omega

/-- `left^4(t)` is not in the pivot's local 5-neighborhood when `n ≥ 8`. -/
theorem left4_not_local5 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    ¬(left (left (left (left t))) = left (left t) ∨
      left (left (left (left t))) = left t ∨
      left (left (left (left t))) = right t ∨
      left (left (left (left t))) = right (right t)) := by
  intro h
  rcases h with h | h | h | h
  · have := congrArg (cwShift t) h
    rw [cwShift_left4_self (by omega) t, cwShift_left2_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_left4_self (by omega) t, cwShift_left_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_left4_self (by omega) t, cwShift_right_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_left4_self (by omega) t, cwShift_right2_self (by omega) t] at this
    omega

/-- `right^3(t)` is not in the pivot's local 5-neighborhood when `n ≥ 8`. -/
theorem right3_not_local5 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    ¬(right (right (right t)) = left (left t) ∨
      right (right (right t)) = left t ∨
      right (right (right t)) = right t ∨
      right (right (right t)) = right (right t)) := by
  intro h
  rcases h with h | h | h | h
  · have := congrArg (cwShift t) h
    rw [cwShift_right3_self (by omega) t, cwShift_left2_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_right3_self (by omega) t, cwShift_left_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_right3_self (by omega) t, cwShift_right_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_right3_self (by omega) t, cwShift_right2_self (by omega) t] at this
    omega

/-- `right^4(t)` is not in the pivot's local 5-neighborhood when `n ≥ 8`. -/
theorem right4_not_local5 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    ¬(right (right (right (right t))) = left (left t) ∨
      right (right (right (right t))) = left t ∨
      right (right (right (right t))) = right t ∨
      right (right (right (right t))) = right (right t)) := by
  intro h
  rcases h with h | h | h | h
  · have := congrArg (cwShift t) h
    rw [cwShift_right4_self (by omega) t, cwShift_left2_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_right4_self (by omega) t, cwShift_left_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_right4_self (by omega) t, cwShift_right_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_right4_self (by omega) t, cwShift_right2_self (by omega) t] at this
    omega

/-- `left t` is not `right t` when `n ≥ 8`. -/
theorem left_ne_right (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    left t ≠ right t := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_left_self (by omega) t, cwShift_right_self (by omega) t] at this
  omega

/-- `right t` is not `left t` when `n ≥ 8`. -/
theorem right_ne_left (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    right t ≠ left t := by
  exact fun h => left_ne_right hn t h.symm

/-- `left^2(t)` is not `right t` when `n ≥ 8`. -/
theorem left2_ne_right (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    left (left t) ≠ right t := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_left2_self (by omega) t, cwShift_right_self (by omega) t] at this
  omega

/-- `right^2(t)` is not `left t` when `n ≥ 8`. -/
theorem right2_ne_left (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    right (right t) ≠ left t := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_right2_self (by omega) t, cwShift_left_self (by omega) t] at this
  omega

/-- `left^4(t)` is not `left^3(t)` when `n ≥ 8`. -/
private theorem left4_ne_left3 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    left (left (left (left t))) ≠ left (left (left t)) := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_left4_self (by omega) t, cwShift_left3_self (by omega) t] at this
  omega

/-- `left^4(t)` is not `t` when `n ≥ 8`. -/
private theorem left4_ne_self (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    left (left (left (left t))) ≠ t := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_left4_self (by omega) t, cwShift_self (by omega) t] at this
  omega

/-- `left^4(t)` is not `right^3(t)` when `n ≥ 8`. -/
private theorem left4_ne_right3 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    left (left (left (left t))) ≠ right (right (right t)) := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_left4_self (by omega) t, cwShift_right3_self (by omega) t] at this
  omega

/-- `right^3(t)` is not `left^4(t)` when `n ≥ 8`. -/
private theorem right3_ne_left4 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    right (right (right t)) ≠ left (left (left (left t))) := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_right3_self (by omega) t, cwShift_left4_self (by omega) t] at this
  omega

/-- `right^3(t)` is not `left^3(t)` when `n ≥ 8`. -/
theorem right3_ne_left3 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    right (right (right t)) ≠ left (left (left t)) := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_right3_self (by omega) t, cwShift_left3_self (by omega) t] at this
  omega

/-- `right^3(t)` is not `t` when `n ≥ 8`. -/
theorem right3_ne_self (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    right (right (right t)) ≠ t := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_right3_self (by omega) t, cwShift_self (by omega) t] at this
  omega

/-- `left^3(t)` is not `t` when `n ≥ 8`. -/
theorem left3_ne_self (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    left (left (left t)) ≠ t := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_left3_self (by omega) t, cwShift_self (by omega) t] at this
  omega

/-- `left^3(t)` is not `right^3(t)` when `n ≥ 8`. -/
theorem left3_ne_right3 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    left (left (left t)) ≠ right (right (right t)) := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_left3_self (by omega) t, cwShift_right3_self (by omega) t] at this
  omega

/-- `left^3(t)` is not `right^2(t)` when `n ≥ 8`. -/
private theorem left3_ne_right2 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    left (left (left t)) ≠ right (right t) := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_left3_self (by omega) t, cwShift_right2_self (by omega) t] at this
  omega

/-- `right^2(t)` is not `left^3(t)` when `n ≥ 8`. -/
theorem right2_ne_left3 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    right (right t) ≠ left (left (left t)) := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_right2_self (by omega) t, cwShift_left3_self (by omega) t] at this
  omega

/-- `right^3(t)` is not `left^2(t)` when `n ≥ 8`. -/
private theorem right3_ne_left2 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    right (right (right t)) ≠ left (left t) := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_right3_self (by omega) t, cwShift_left2_self (by omega) t] at this
  omega

/-- `left^2(t)` is not `right^3(t)` when `n ≥ 8`. -/
theorem left2_ne_right3 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    left (left t) ≠ right (right (right t)) := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_left2_self (by omega) t, cwShift_right3_self (by omega) t] at this
  omega

/-- `right^2(t)` is not `left^2(t)` when `n ≥ 8`. -/
theorem right2_ne_left2 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    right (right t) ≠ left (left t) := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_right2_self (by omega) t, cwShift_left2_self (by omega) t] at this
  omega

/-- `left^2(t)` is not `right^2(t)` when `n ≥ 8`. -/
theorem left2_ne_right2 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    left (left t) ≠ right (right t) := by
  exact fun h => right2_ne_left2 hn t h.symm

/-- `left^3(t)` is not `right^4(t)` when `n ≥ 8`. -/
private theorem left3_ne_right4 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    left (left (left t)) ≠ right (right (right (right t))) := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_left3_self (by omega) t, cwShift_right4_self (by omega) t] at this
  omega

/-- `right^4(t)` is not `left^3(t)` when `n ≥ 8`. -/
private theorem right4_ne_left3 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    right (right (right (right t))) ≠ left (left (left t)) := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_right4_self (by omega) t, cwShift_left3_self (by omega) t] at this
  omega

/-- `right^4(t)` is not `t` when `n ≥ 8`. -/
private theorem right4_ne_self (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    right (right (right (right t))) ≠ t := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_right4_self (by omega) t, cwShift_self (by omega) t] at this
  omega

/-- `right^4(t)` is not `right^3(t)` when `n ≥ 8`. -/
private theorem right4_ne_right3 (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    right (right (right (right t))) ≠ right (right (right t)) := by
  intro h
  have := congrArg (cwShift t) h
  rw [cwShift_right4_self (by omega) t, cwShift_right3_self (by omega) t] at this
  omega

/-- Exact CW displacement of `left^5 p` from `right p`. -/
private theorem cwShift_left5_self {n : Nat} (hn : n ≥ 8) (p : Fin n) :
    cwShift p (left (left (left (left (left p))))) = n - 6 := by
  have hN7 : n ≥ 7 := by omega
  have hpos : 0 < cwShift p (left (left (left (left p)))) := by
    rw [cwShift_left4_self hN7 p]
    omega
  rw [cwShift_left_step (by omega) p (left (left (left (left p)))) hpos,
    cwShift_left4_self hN7 p]
  omega

/-- Exact CW displacement of `right^5 p` from `right p`. -/
private theorem cwShift_right5_self {n : Nat} (hn : n ≥ 8) (p : Fin n) :
    cwShift p (right (right (right (right (right p))))) = 4 := by
  have hN6 : n ≥ 6 := by omega
  have hlt : cwShift p (right (right (right (right p)))) < n - 1 := by
    rw [cwShift_right4_self hN6 p]
    omega
  rw [cwShift_right_step (by omega) p (right (right (right (right p)))) hlt,
    cwShift_right4_self hN6 p]

/-- `left^4(t)` is not in the left-biased 6-neighborhood. -/
private theorem left4_not_leftsix (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    ¬(left (left (left (left t))) = left (left (left t)) ∨
      left (left (left (left t))) = left (left t) ∨
      left (left (left (left t))) = left t ∨
      left (left (left (left t))) = t ∨
      left (left (left (left t))) = right t ∨
      left (left (left (left t))) = right (right t)) := by
  intro h
  rcases h with h | h | h | h | h | h
  · exact left4_ne_left3 hn t h
  · exact (left4_not_local5 hn t) (Or.inl h)
  · exact (left4_not_local5 hn t) (Or.inr (Or.inl h))
  · exact left4_ne_self hn t h
  · exact (left4_not_local5 hn t) (Or.inr (Or.inr (Or.inl h)))
  · exact (left4_not_local5 hn t) (Or.inr (Or.inr (Or.inr h)))

/-- `right^3(t)` is not in the left-biased 6-neighborhood. -/
theorem right3_not_leftsix (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    ¬(right (right (right t)) = left (left (left t)) ∨
      right (right (right t)) = left (left t) ∨
      right (right (right t)) = left t ∨
      right (right (right t)) = t ∨
      right (right (right t)) = right t ∨
      right (right (right t)) = right (right t)) := by
  intro h
  rcases h with h | h | h | h | h | h
  · exact right3_ne_left3 hn t h
  · exact (right3_not_local5 hn t) (Or.inl h)
  · exact (right3_not_local5 hn t) (Or.inr (Or.inl h))
  · exact right3_ne_self hn t h
  · exact (right3_not_local5 hn t) (Or.inr (Or.inr (Or.inl h)))
  · exact (right3_not_local5 hn t) (Or.inr (Or.inr (Or.inr h)))

/-- `right^4(t)` is not in the left-biased 6-neighborhood. -/
private theorem right4_not_leftsix (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    ¬(right (right (right (right t))) = left (left (left t)) ∨
      right (right (right (right t))) = left (left t) ∨
      right (right (right (right t))) = left t ∨
      right (right (right (right t))) = t ∨
      right (right (right (right t))) = right t ∨
      right (right (right (right t))) = right (right t)) := by
  intro h
  rcases h with h | h | h | h | h | h
  · exact right4_ne_left3 hn t h
  · exact (right4_not_local5 hn t) (Or.inl h)
  · exact (right4_not_local5 hn t) (Or.inr (Or.inl h))
  · exact right4_ne_self hn t h
  · exact (right4_not_local5 hn t) (Or.inr (Or.inr (Or.inl h)))
  · exact (right4_not_local5 hn t) (Or.inr (Or.inr (Or.inr h)))

/-- `left^5(t)` is not in the left-biased 6-neighborhood. -/
private theorem left5_not_leftsix (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    ¬(left (left (left (left (left t)))) = left (left (left t)) ∨
      left (left (left (left (left t)))) = left (left t) ∨
      left (left (left (left (left t)))) = left t ∨
      left (left (left (left (left t)))) = t ∨
      left (left (left (left (left t)))) = right t ∨
      left (left (left (left (left t)))) = right (right t)) := by
  intro h
  rcases h with h | h | h | h | h | h
  · have := congrArg (cwShift t) h
    rw [cwShift_left5_self hn t, cwShift_left3_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_left5_self hn t, cwShift_left2_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_left5_self hn t, cwShift_left_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_left5_self hn t, cwShift_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_left5_self hn t, cwShift_right_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_left5_self hn t, cwShift_right2_self (by omega) t] at this
    omega

/-- `left^3(t)` is not in the right-biased 6-neighborhood. -/
theorem left3_not_rightsix (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    ¬(left (left (left t)) = left (left t) ∨
      left (left (left t)) = left t ∨
      left (left (left t)) = t ∨
      left (left (left t)) = right t ∨
      left (left (left t)) = right (right t) ∨
      left (left (left t)) = right (right (right t))) := by
  intro h
  rcases h with h | h | h | h | h | h
  · exact (left3_not_local5 hn t) (Or.inl h)
  · exact (left3_not_local5 hn t) (Or.inr (Or.inl h))
  · exact left3_ne_self hn t h
  · exact (left3_not_local5 hn t) (Or.inr (Or.inr (Or.inl h)))
  · exact (left3_not_local5 hn t) (Or.inr (Or.inr (Or.inr h)))
  · exact left3_ne_right3 hn t h

/-- `left^4(t)` is not in the right-biased 6-neighborhood. -/
private theorem left4_not_rightsix (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    ¬(left (left (left (left t))) = left (left t) ∨
      left (left (left (left t))) = left t ∨
      left (left (left (left t))) = t ∨
      left (left (left (left t))) = right t ∨
      left (left (left (left t))) = right (right t) ∨
      left (left (left (left t))) = right (right (right t))) := by
  intro h
  rcases h with h | h | h | h | h | h
  · exact (left4_not_local5 hn t) (Or.inl h)
  · exact (left4_not_local5 hn t) (Or.inr (Or.inl h))
  · exact left4_ne_self hn t h
  · exact (left4_not_local5 hn t) (Or.inr (Or.inr (Or.inl h)))
  · exact (left4_not_local5 hn t) (Or.inr (Or.inr (Or.inr h)))
  · exact left4_ne_right3 hn t h

/-- `right^4(t)` is not in the right-biased 6-neighborhood. -/
private theorem right4_not_rightsix (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    ¬(right (right (right (right t))) = left (left t) ∨
      right (right (right (right t))) = left t ∨
      right (right (right (right t))) = t ∨
      right (right (right (right t))) = right t ∨
      right (right (right (right t))) = right (right t) ∨
      right (right (right (right t))) = right (right (right t))) := by
  intro h
  rcases h with h | h | h | h | h | h
  · exact (right4_not_local5 hn t) (Or.inl h)
  · exact (right4_not_local5 hn t) (Or.inr (Or.inl h))
  · exact right4_ne_self hn t h
  · exact (right4_not_local5 hn t) (Or.inr (Or.inr (Or.inl h)))
  · exact (right4_not_local5 hn t) (Or.inr (Or.inr (Or.inr h)))
  · exact right4_ne_right3 hn t h

/-- `right^5(t)` is not in the right-biased 6-neighborhood. -/
private theorem right5_not_rightsix (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n) :
    ¬(right (right (right (right (right t)))) = left (left t) ∨
      right (right (right (right (right t)))) = left t ∨
      right (right (right (right (right t)))) = t ∨
      right (right (right (right (right t)))) = right t ∨
      right (right (right (right (right t)))) = right (right t) ∨
      right (right (right (right (right t)))) = right (right (right t))) := by
  intro h
  rcases h with h | h | h | h | h | h
  · have := congrArg (cwShift t) h
    rw [cwShift_right5_self (by omega) t, cwShift_left2_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_right5_self (by omega) t, cwShift_left_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_right5_self (by omega) t, cwShift_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_right5_self (by omega) t, cwShift_right_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_right5_self (by omega) t, cwShift_right2_self (by omega) t] at this
    omega
  · have := congrArg (cwShift t) h
    rw [cwShift_right5_self (by omega) t, cwShift_right3_self (by omega) t] at this
    omega

/-- A left-biased prefix-edge witness has a deterministic immediate successor. -/
theorem left_prefix_edge_successor_shape
    (gc : GoodCycle sys) (t : Fin sys.rs.n) (hn : sys.rs.n ≥ 8)
    (j : Fin gc.configs.length)
    (hj1_lt_len : j.val + 1 < gc.configs.length)
    (hj_edge :
      gc.moverAt j = left (left (left (left t))) ∨
      gc.moverAt j = right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t ∨
        gc.moverAt k = t ∨
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t)) :
    (gc.moverAt j = left (left (left (left t))) ∧
      gc.moverAt ⟨j.val + 1, hj1_lt_len⟩ = left (left (left t))) ∨
    (gc.moverAt j = right (right (right t)) ∧
      gc.moverAt ⟨j.val + 1, hj1_lt_len⟩ = right (right t)) := by
  let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
  have hj1_eq_next : nextIndex gc.configs j = j1 := by
    apply Fin.ext
    simp [nextIndex, j1]
    exact Nat.mod_eq_of_lt hj1_lt_len
  have hj1_tail := hj_tail j1 (by
    dsimp [j1]
    omega)
  have hnext_local := gc.next_mover_is_local j
  rw [hj1_eq_next] at hnext_local
  rcases hj_edge with hj_left4 | hj_right3
  · rcases hnext_local with hleft | hself | hright
    · exfalso
      have hj1_left5 : gc.moverAt j1 = left (left (left (left (left t)))) := by
        simpa [hj_left4] using hleft
      apply left5_not_leftsix hn t
      rcases hj1_tail with hj | hj | hj | hj | hj | hj
      · exact Or.inl (by calc
          left (left (left (left (left t)))) = gc.moverAt j1 := hj1_left5.symm
          _ = left (left (left t)) := hj)
      · exact Or.inr (Or.inl (by calc
          left (left (left (left (left t)))) = gc.moverAt j1 := hj1_left5.symm
          _ = left (left t) := hj))
      · exact Or.inr (Or.inr (Or.inl (by calc
          left (left (left (left (left t)))) = gc.moverAt j1 := hj1_left5.symm
          _ = left t := hj)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by calc
          left (left (left (left (left t)))) = gc.moverAt j1 := hj1_left5.symm
          _ = t := hj))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by calc
          left (left (left (left (left t)))) = gc.moverAt j1 := hj1_left5.symm
          _ = right t := hj)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by calc
          left (left (left (left (left t)))) = gc.moverAt j1 := hj1_left5.symm
          _ = right (right t) := hj)))))
    · exfalso
      have hj1_left4 : gc.moverAt j1 = left (left (left (left t))) := by
        simpa [hj_left4] using hself
      apply left4_not_leftsix hn t
      rcases hj1_tail with hj | hj | hj | hj | hj | hj
      · exact Or.inl (by calc
          left (left (left (left t))) = gc.moverAt j1 := hj1_left4.symm
          _ = left (left (left t)) := hj)
      · exact Or.inr (Or.inl (by calc
          left (left (left (left t))) = gc.moverAt j1 := hj1_left4.symm
          _ = left (left t) := hj))
      · exact Or.inr (Or.inr (Or.inl (by calc
          left (left (left (left t))) = gc.moverAt j1 := hj1_left4.symm
          _ = left t := hj)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by calc
          left (left (left (left t))) = gc.moverAt j1 := hj1_left4.symm
          _ = t := hj))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by calc
          left (left (left (left t))) = gc.moverAt j1 := hj1_left4.symm
          _ = right t := hj)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by calc
          left (left (left (left t))) = gc.moverAt j1 := hj1_left4.symm
          _ = right (right t) := hj)))))
    · exact Or.inl ⟨hj_left4, by simpa [hj_left4, j1] using hright⟩
  · rcases hnext_local with hleft | hself | hright
    · exact Or.inr ⟨hj_right3, by simpa [hj_right3, j1] using hleft⟩
    · exfalso
      have hj1_right3 : gc.moverAt j1 = right (right (right t)) := by
        simpa [hj_right3] using hself
      apply right3_not_leftsix hn t
      rcases hj1_tail with hj | hj | hj | hj | hj | hj
      · exact Or.inl (by calc
          right (right (right t)) = gc.moverAt j1 := hj1_right3.symm
          _ = left (left (left t)) := hj)
      · exact Or.inr (Or.inl (by calc
          right (right (right t)) = gc.moverAt j1 := hj1_right3.symm
          _ = left (left t) := hj))
      · exact Or.inr (Or.inr (Or.inl (by calc
          right (right (right t)) = gc.moverAt j1 := hj1_right3.symm
          _ = left t := hj)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by calc
          right (right (right t)) = gc.moverAt j1 := hj1_right3.symm
          _ = t := hj))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by calc
          right (right (right t)) = gc.moverAt j1 := hj1_right3.symm
          _ = right t := hj)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by calc
          right (right (right t)) = gc.moverAt j1 := hj1_right3.symm
          _ = right (right t) := hj)))))
    · exfalso
      have hj1_right4 : gc.moverAt j1 = right (right (right (right t))) := by
        simpa [hj_right3] using hright
      apply right4_not_leftsix hn t
      rcases hj1_tail with hj | hj | hj | hj | hj | hj
      · exact Or.inl (by calc
          right (right (right (right t))) = gc.moverAt j1 := hj1_right4.symm
          _ = left (left (left t)) := hj)
      · exact Or.inr (Or.inl (by calc
          right (right (right (right t))) = gc.moverAt j1 := hj1_right4.symm
          _ = left (left t) := hj))
      · exact Or.inr (Or.inr (Or.inl (by calc
          right (right (right (right t))) = gc.moverAt j1 := hj1_right4.symm
          _ = left t := hj)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by calc
          right (right (right (right t))) = gc.moverAt j1 := hj1_right4.symm
          _ = t := hj))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by calc
          right (right (right (right t))) = gc.moverAt j1 := hj1_right4.symm
          _ = right t := hj)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by calc
          right (right (right (right t))) = gc.moverAt j1 := hj1_right4.symm
          _ = right (right t) := hj)))))

/-- A right-biased prefix-edge witness has a deterministic immediate successor. -/
theorem right_prefix_edge_successor_shape
    (gc : GoodCycle sys) (t : Fin sys.rs.n) (hn : sys.rs.n ≥ 8)
    (j : Fin gc.configs.length)
    (hj1_lt_len : j.val + 1 < gc.configs.length)
    (hj_edge :
      gc.moverAt j = left (left (left t)) ∨
      gc.moverAt j = right (right (right (right t))))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j.val < k.val →
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t ∨
        gc.moverAt k = t ∨
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t) ∨
        gc.moverAt k = right (right (right t))) :
    (gc.moverAt j = left (left (left t)) ∧
      gc.moverAt ⟨j.val + 1, hj1_lt_len⟩ = left (left t)) ∨
    (gc.moverAt j = right (right (right (right t))) ∧
      gc.moverAt ⟨j.val + 1, hj1_lt_len⟩ = right (right (right t))) := by
  let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
  have hj1_eq_next : nextIndex gc.configs j = j1 := by
    apply Fin.ext
    simp [nextIndex, j1]
    exact Nat.mod_eq_of_lt hj1_lt_len
  have hj1_tail := hj_tail j1 (by
    dsimp [j1]
    omega)
  have hnext_local := gc.next_mover_is_local j
  rw [hj1_eq_next] at hnext_local
  rcases hj_edge with hj_left3 | hj_right4
  · rcases hnext_local with hleft | hself | hright
    · exfalso
      have hj1_left4 : gc.moverAt j1 = left (left (left (left t))) := by
        simpa [hj_left3] using hleft
      apply left4_not_rightsix hn t
      rcases hj1_tail with hj | hj | hj | hj | hj | hj
      · exact Or.inl (by calc
          left (left (left (left t))) = gc.moverAt j1 := hj1_left4.symm
          _ = left (left t) := hj)
      · exact Or.inr (Or.inl (by calc
          left (left (left (left t))) = gc.moverAt j1 := hj1_left4.symm
          _ = left t := hj))
      · exact Or.inr (Or.inr (Or.inl (by calc
          left (left (left (left t))) = gc.moverAt j1 := hj1_left4.symm
          _ = t := hj)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by calc
          left (left (left (left t))) = gc.moverAt j1 := hj1_left4.symm
          _ = right t := hj))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by calc
          left (left (left (left t))) = gc.moverAt j1 := hj1_left4.symm
          _ = right (right t) := hj)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by calc
          left (left (left (left t))) = gc.moverAt j1 := hj1_left4.symm
          _ = right (right (right t)) := hj)))))
    · exfalso
      have hj1_left3 : gc.moverAt j1 = left (left (left t)) := by
        simpa [hj_left3] using hself
      apply left3_not_rightsix hn t
      rcases hj1_tail with hj | hj | hj | hj | hj | hj
      · exact Or.inl (by calc
          left (left (left t)) = gc.moverAt j1 := hj1_left3.symm
          _ = left (left t) := hj)
      · exact Or.inr (Or.inl (by calc
          left (left (left t)) = gc.moverAt j1 := hj1_left3.symm
          _ = left t := hj))
      · exact Or.inr (Or.inr (Or.inl (by calc
          left (left (left t)) = gc.moverAt j1 := hj1_left3.symm
          _ = t := hj)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by calc
          left (left (left t)) = gc.moverAt j1 := hj1_left3.symm
          _ = right t := hj))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by calc
          left (left (left t)) = gc.moverAt j1 := hj1_left3.symm
          _ = right (right t) := hj)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by calc
          left (left (left t)) = gc.moverAt j1 := hj1_left3.symm
          _ = right (right (right t)) := hj)))))
    · exact Or.inl ⟨hj_left3, by simpa [hj_left3, j1] using hright⟩
  · rcases hnext_local with hleft | hself | hright
    · exact Or.inr ⟨hj_right4, by simpa [hj_right4, j1] using hleft⟩
    · exfalso
      have hj1_right4 : gc.moverAt j1 = right (right (right (right t))) := by
        simpa [hj_right4] using hself
      apply right4_not_rightsix hn t
      rcases hj1_tail with hj | hj | hj | hj | hj | hj
      · exact Or.inl (by calc
          right (right (right (right t))) = gc.moverAt j1 := hj1_right4.symm
          _ = left (left t) := hj)
      · exact Or.inr (Or.inl (by calc
          right (right (right (right t))) = gc.moverAt j1 := hj1_right4.symm
          _ = left t := hj))
      · exact Or.inr (Or.inr (Or.inl (by calc
          right (right (right (right t))) = gc.moverAt j1 := hj1_right4.symm
          _ = t := hj)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by calc
          right (right (right (right t))) = gc.moverAt j1 := hj1_right4.symm
          _ = right t := hj))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by calc
          right (right (right (right t))) = gc.moverAt j1 := hj1_right4.symm
          _ = right (right t) := hj)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by calc
          right (right (right (right t))) = gc.moverAt j1 := hj1_right4.symm
          _ = right (right (right t)) := hj)))))
    · exfalso
      have hj1_right5 : gc.moverAt j1 = right (right (right (right (right t)))) := by
        simpa [hj_right4] using hright
      apply right5_not_rightsix hn t
      rcases hj1_tail with hj | hj | hj | hj | hj | hj
      · exact Or.inl (by calc
          right (right (right (right (right t)))) = gc.moverAt j1 := hj1_right5.symm
          _ = left (left t) := hj)
      · exact Or.inr (Or.inl (by calc
          right (right (right (right (right t)))) = gc.moverAt j1 := hj1_right5.symm
          _ = left t := hj))
      · exact Or.inr (Or.inr (Or.inl (by calc
          right (right (right (right (right t)))) = gc.moverAt j1 := hj1_right5.symm
          _ = t := hj)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by calc
          right (right (right (right (right t)))) = gc.moverAt j1 := hj1_right5.symm
          _ = right t := hj))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by calc
          right (right (right (right (right t)))) = gc.moverAt j1 := hj1_right5.symm
          _ = right (right t) := hj)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by calc
          right (right (right (right (right t)))) = gc.moverAt j1 := hj1_right5.symm
          _ = right (right (right t)) := hj)))))


/-- Once a phase tail enters at `left^3(t)` and all later movers stay in the
    pivot's local 5-neighborhood, the tail cannot cross to the right side before
    the final `t`-fire. -/
private theorem phase_tail_from_left3_stays_left
    (gc : GoodCycle sys) (t : Fin sys.rs.n) (phase : TernaryPhase gc t)
    (hn : sys.rs.n ≥ 8)
    (a0 : Fin gc.configs.length)
    (ha0_ge_a : phase.a.val ≤ a0.val)
    (ha0_lt_s : a0.val < phase.s.val)
    (ha0_left3 : gc.moverAt a0 = left (left (left t)))
    (htail5 : ∀ k : Fin gc.configs.length,
      a0.val < k.val → k.val < phase.s.val →
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t)) :
    ∀ k : Fin gc.configs.length,
      a0.val ≤ k.val → k.val < phase.s.val →
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t := by
  intro k hk_ge hk_lt
  by_cases hgood :
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t
  · exact hgood
  · let badSet : Finset (Fin gc.configs.length) :=
      (Finset.univ : Finset (Fin gc.configs.length)).filter
        (fun j =>
          a0.val ≤ j.val ∧ j.val < phase.s.val ∧
          gc.moverAt j ≠ left (left (left t)) ∧
          gc.moverAt j ≠ left (left t) ∧
          gc.moverAt j ≠ left t)
    push_neg at hgood
    have hk_mem : k ∈ badSet := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ k, ?_⟩
      simp [badSet, hk_ge, hk_lt, hgood]
    have hne : badSet.Nonempty := ⟨k, hk_mem⟩
    obtain ⟨j, hj_mem, hj_min⟩ := Finset.exists_min_image badSet Fin.val hne
    have hj_ge : a0.val ≤ j.val := by
      simp [badSet] at hj_mem
      exact hj_mem.1
    have hj_lt : j.val < phase.s.val := by
      simp [badSet] at hj_mem
      exact hj_mem.2.1
    have hj_bad :
        ¬(gc.moverAt j = left (left (left t)) ∨
          gc.moverAt j = left (left t) ∨
          gc.moverAt j = left t) := by
      simp [badSet] at hj_mem
      rcases hj_mem.2.2 with ⟨hj3, hj2, hj1⟩
      intro h
      rcases h with h | h | h
      · exact hj3 h
      · exact hj2 h
      · exact hj1 h
    have hj_ne_a0 : j ≠ a0 := by
      intro hEq
      apply hj_bad
      left
      simpa [hEq] using ha0_left3
    have hj_gt : a0.val < j.val := by
      have hneq : j.val ≠ a0.val := by
        intro hval
        exact hj_ne_a0 (Fin.ext hval)
      omega
    let prev : Fin gc.configs.length := ⟨j.val - 1, by omega⟩
    have hprev_lt_j : prev.val < j.val := by
      dsimp [prev]
      omega
    have hprev_ge : a0.val ≤ prev.val := by
      dsimp [prev]
      omega
    have hprev_lt_s : prev.val < phase.s.val := by
      dsimp [prev]
      omega
    have hprev_not_mem : prev ∉ badSet := by
      intro hmem
      have hle := hj_min prev hmem
      have : j.val ≤ j.val - 1 := by
        simpa [prev] using hle
      omega
    have hprev_good :
        gc.moverAt prev = left (left (left t)) ∨
        gc.moverAt prev = left (left t) ∨
        gc.moverAt prev = left t := by
      by_cases hprev_good :
          gc.moverAt prev = left (left (left t)) ∨
          gc.moverAt prev = left (left t) ∨
          gc.moverAt prev = left t
      · exact hprev_good
      · exfalso
        push_neg at hprev_good
        exact hprev_not_mem (by
          refine Finset.mem_filter.mpr ?_
          refine ⟨Finset.mem_univ prev, ?_⟩
          simp [badSet, hprev_ge, hprev_lt_s, hprev_good])
    have hj_ge_a : phase.a.val ≤ j.val := by omega
    have hj_nonmover : gc.moverAt j ≠ t := phase.ht_nofire j hj_ge_a hj_lt
    have hnext_eq : nextIndex gc.configs prev = j := by
      apply Fin.ext
      have hsucc : prev.val + 1 = j.val := by
        dsimp [prev]
        omega
      simp [nextIndex, prev, hsucc, Nat.mod_eq_of_lt j.isLt]
    have hnext_local := gc.next_mover_is_local prev
    rw [hnext_eq] at hnext_local
    have hj_local5 :
        gc.moverAt j = left (left t) ∨
        gc.moverAt j = left t ∨
        gc.moverAt j = right t ∨
        gc.moverAt j = right (right t) := by
      exact htail5 j hj_gt hj_lt
    have hj_good :
        gc.moverAt j = left (left (left t)) ∨
        gc.moverAt j = left (left t) ∨
        gc.moverAt j = left t := by
      rcases hprev_good with hprev3 | hprev2 | hprev1
      · rcases hnext_local with hleft | hself | hright
        · exfalso
          have hj_l4 : gc.moverAt j = left (left (left (left t))) := by
            simpa [hprev3] using hleft
          apply left4_not_local5 hn t
          rcases hj_local5 with hjll | hjl | hjr | hjrr
          · exact Or.inl (by rw [← hj_l4, hjll])
          · exact Or.inr (Or.inl (by rw [← hj_l4, hjl]))
          · exact Or.inr (Or.inr (Or.inl (by rw [← hj_l4, hjr])))
          · exact Or.inr (Or.inr (Or.inr (by rw [← hj_l4, hjrr])))
        · exfalso
          have hj_l3 : gc.moverAt j = left (left (left t)) := by
            simpa [hprev3] using hself
          apply left3_not_local5 hn t
          rcases hj_local5 with hjll | hjl | hjr | hjrr
          · exact Or.inl (by rw [← hj_l3, hjll])
          · exact Or.inr (Or.inl (by rw [← hj_l3, hjl]))
          · exact Or.inr (Or.inr (Or.inl (by rw [← hj_l3, hjr])))
          · exact Or.inr (Or.inr (Or.inr (by rw [← hj_l3, hjrr])))
        · exact Or.inr (Or.inl (by simpa [hprev3] using hright))
      · rcases hnext_local with hleft | hself | hright
        · exfalso
          have hj_l3 : gc.moverAt j = left (left (left t)) := by
            simpa [hprev2] using hleft
          apply left3_not_local5 hn t
          rcases hj_local5 with hjll | hjl | hjr | hjrr
          · exact Or.inl (by rw [← hj_l3, hjll])
          · exact Or.inr (Or.inl (by rw [← hj_l3, hjl]))
          · exact Or.inr (Or.inr (Or.inl (by rw [← hj_l3, hjr])))
          · exact Or.inr (Or.inr (Or.inr (by rw [← hj_l3, hjrr])))
        · exact Or.inr (Or.inl (by simpa [hprev2] using hself))
        · exact Or.inr (Or.inr (by simpa [hprev2] using hright))
      · rcases hnext_local with hleft | hself | hright
        · exact Or.inr (Or.inl (by simpa [hprev1] using hleft))
        · exact Or.inr (Or.inr (by simpa [hprev1] using hself))
        · exfalso
          exact hj_nonmover (by simpa [hprev1] using hright)
    exact False.elim (hj_bad hj_good)

/-- Symmetric right-sided phase-tail invariance lemma. -/
private theorem phase_tail_from_right3_stays_right
    (gc : GoodCycle sys) (t : Fin sys.rs.n) (phase : TernaryPhase gc t)
    (hn : sys.rs.n ≥ 8)
    (a0 : Fin gc.configs.length)
    (ha0_ge_a : phase.a.val ≤ a0.val)
    (ha0_lt_s : a0.val < phase.s.val)
    (ha0_right3 : gc.moverAt a0 = right (right (right t)))
    (htail5 : ∀ k : Fin gc.configs.length,
      a0.val < k.val → k.val < phase.s.val →
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t)) :
    ∀ k : Fin gc.configs.length,
      a0.val ≤ k.val → k.val < phase.s.val →
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t)) := by
  intro k hk_ge hk_lt
  by_cases hgood :
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t))
  · exact hgood
  · let badSet : Finset (Fin gc.configs.length) :=
      (Finset.univ : Finset (Fin gc.configs.length)).filter
        (fun j =>
          a0.val ≤ j.val ∧ j.val < phase.s.val ∧
          gc.moverAt j ≠ right t ∧
          gc.moverAt j ≠ right (right t) ∧
          gc.moverAt j ≠ right (right (right t)))
    push_neg at hgood
    have hk_mem : k ∈ badSet := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ k, ?_⟩
      simp [badSet, hk_ge, hk_lt, hgood]
    have hne : badSet.Nonempty := ⟨k, hk_mem⟩
    obtain ⟨j, hj_mem, hj_min⟩ := Finset.exists_min_image badSet Fin.val hne
    have hj_ge : a0.val ≤ j.val := by
      simp [badSet] at hj_mem
      exact hj_mem.1
    have hj_lt : j.val < phase.s.val := by
      simp [badSet] at hj_mem
      exact hj_mem.2.1
    have hj_bad :
        ¬(gc.moverAt j = right t ∨
          gc.moverAt j = right (right t) ∨
          gc.moverAt j = right (right (right t))) := by
      simp [badSet] at hj_mem
      rcases hj_mem.2.2 with ⟨hj1, hj2, hj3⟩
      intro h
      rcases h with h | h | h
      · exact hj1 h
      · exact hj2 h
      · exact hj3 h
    have hj_ne_a0 : j ≠ a0 := by
      intro hEq
      apply hj_bad
      exact Or.inr (Or.inr (by simpa [hEq] using ha0_right3))
    have hj_gt : a0.val < j.val := by
      have hneq : j.val ≠ a0.val := by
        intro hval
        exact hj_ne_a0 (Fin.ext hval)
      omega
    let prev : Fin gc.configs.length := ⟨j.val - 1, by omega⟩
    have hprev_lt_j : prev.val < j.val := by
      dsimp [prev]
      omega
    have hprev_ge : a0.val ≤ prev.val := by
      dsimp [prev]
      omega
    have hprev_lt_s : prev.val < phase.s.val := by
      dsimp [prev]
      omega
    have hprev_not_mem : prev ∉ badSet := by
      intro hmem
      have := hj_min prev hmem
      exact False.elim (by omega)
    have hprev_good :
        gc.moverAt prev = right t ∨
        gc.moverAt prev = right (right t) ∨
        gc.moverAt prev = right (right (right t)) := by
      by_cases hprev_good :
          gc.moverAt prev = right t ∨
          gc.moverAt prev = right (right t) ∨
          gc.moverAt prev = right (right (right t))
      · exact hprev_good
      · exfalso
        push_neg at hprev_good
        exact hprev_not_mem (by
          refine Finset.mem_filter.mpr ?_
          refine ⟨Finset.mem_univ prev, ?_⟩
          simp [badSet, hprev_ge, hprev_lt_s, hprev_good])
    have hj_ge_a : phase.a.val ≤ j.val := by omega
    have hj_nonmover : gc.moverAt j ≠ t := phase.ht_nofire j hj_ge_a hj_lt
    have hnext_eq : nextIndex gc.configs prev = j := by
      apply Fin.ext
      have hsucc : prev.val + 1 = j.val := by
        dsimp [prev]
        omega
      simp [nextIndex, prev, hsucc, Nat.mod_eq_of_lt j.isLt]
    have hnext_local := gc.next_mover_is_local prev
    rw [hnext_eq] at hnext_local
    have hj_local5 :
        gc.moverAt j = left (left t) ∨
        gc.moverAt j = left t ∨
        gc.moverAt j = right t ∨
        gc.moverAt j = right (right t) := by
      exact htail5 j hj_gt hj_lt
    have hj_good :
        gc.moverAt j = right t ∨
        gc.moverAt j = right (right t) ∨
        gc.moverAt j = right (right (right t)) := by
      rcases hprev_good with hprev1 | hprev2 | hprev3
      · rcases hnext_local with hleft | hself | hright
        · exfalso
          exact hj_nonmover (by simpa [hprev1] using hleft)
        · exact Or.inl (by simpa [hprev1] using hself)
        · exact Or.inr (Or.inl (by simpa [hprev1] using hright))
      · rcases hnext_local with hleft | hself | hright
        · exact Or.inl (by simpa [hprev2] using hleft)
        · exact Or.inr (Or.inl (by simpa [hprev2] using hself))
        · exfalso
          have hj_r3 : gc.moverAt j = right (right (right t)) := by
            simpa [hprev2] using hright
          apply right3_not_local5 hn t
          rcases hj_local5 with hjll | hjl | hjr | hjrr
          · exact Or.inl (by rw [← hj_r3, hjll])
          · exact Or.inr (Or.inl (by rw [← hj_r3, hjl]))
          · exact Or.inr (Or.inr (Or.inl (by rw [← hj_r3, hjr])))
          · exact Or.inr (Or.inr (Or.inr (by rw [← hj_r3, hjrr])))
      · rcases hnext_local with hleft | hself | hright
        · exact Or.inr (Or.inl (by simpa [hprev3] using hleft))
        · exfalso
          have hj_r3 : gc.moverAt j = right (right (right t)) := by
            simpa [hprev3] using hself
          apply right3_not_local5 hn t
          rcases hj_local5 with hjll | hjl | hjr | hjrr
          · exact Or.inl (by rw [← hj_r3, hjll])
          · exact Or.inr (Or.inl (by rw [← hj_r3, hjl]))
          · exact Or.inr (Or.inr (Or.inl (by rw [← hj_r3, hjr])))
          · exact Or.inr (Or.inr (Or.inr (by rw [← hj_r3, hjrr])))
        · exfalso
          have hj_r4 : gc.moverAt j = right (right (right (right t))) := by
            simpa [hprev3] using hright
          apply right4_not_local5 hn t
          rcases hj_local5 with hjll | hjl | hjr | hjrr
          · exact Or.inl (by rw [← hj_r4, hjll])
          · exact Or.inr (Or.inl (by rw [← hj_r4, hjl]))
          · exact Or.inr (Or.inr (Or.inl (by rw [← hj_r4, hjr])))
          · exact Or.inr (Or.inr (Or.inr (by rw [← hj_r4, hjrr])))
    exact False.elim (hj_bad hj_good)

/-- If the last outside mover of a phase sits at `left^3(t)` or `right^3(t)`,
    and every later mover before the final `t`-fire is local to the pivot, then
    the whole remaining phase tail is one-sided. -/
theorem last_outside_phase_tail_one_sided
    (gc : GoodCycle sys) (t : Fin sys.rs.n) (phase : TernaryPhase gc t)
    (hn : sys.rs.n ≥ 8)
    (a0 : Fin gc.configs.length)
    (ha0_ge_a : phase.a.val ≤ a0.val)
    (ha0_lt_s : a0.val < phase.s.val)
    (ha0_side :
      gc.moverAt a0 = left (left (left t)) ∨
      gc.moverAt a0 = right (right (right t)))
    (htail5 : ∀ k : Fin gc.configs.length,
      a0.val < k.val → k.val < phase.s.val →
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t)) :
    (∀ k : Fin gc.configs.length,
      a0.val ≤ k.val → k.val < phase.s.val →
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t) ∨
    (∀ k : Fin gc.configs.length,
      a0.val ≤ k.val → k.val < phase.s.val →
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t))) := by
  rcases ha0_side with ha0_left | ha0_right
  · exact Or.inl (phase_tail_from_left3_stays_left gc t phase hn a0
      ha0_ge_a ha0_lt_s ha0_left htail5)
  · exact Or.inr (phase_tail_from_right3_stays_right gc t phase hn a0
      ha0_ge_a ha0_lt_s ha0_right htail5)

/-- Strengthened phase-tail left invariance: repeated `left^3(t)` steps are
    allowed in the phase tail. If the tail stays inside the pivot's
    6-neighborhood before the final `t`-fire, then it still remains entirely
    on the left side. -/
theorem phase_tail_from_left3_stays_left6
    (gc : GoodCycle sys) (t : Fin sys.rs.n) (phase : TernaryPhase gc t)
    (hn : sys.rs.n ≥ 8)
    (a0 : Fin gc.configs.length)
    (ha0_ge_a : phase.a.val ≤ a0.val)
    (ha0_lt_s : a0.val < phase.s.val)
    (ha0_left3 : gc.moverAt a0 = left (left (left t)))
    (htail6 : ∀ k : Fin gc.configs.length,
      a0.val < k.val → k.val < phase.s.val →
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t))) :
    ∀ k : Fin gc.configs.length,
      a0.val ≤ k.val → k.val < phase.s.val →
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t := by
  intro k hk_ge hk_lt
  by_cases hgood :
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t
  · exact hgood
  · let badSet : Finset (Fin gc.configs.length) :=
      (Finset.univ : Finset (Fin gc.configs.length)).filter
        (fun j =>
          a0.val ≤ j.val ∧ j.val < phase.s.val ∧
          gc.moverAt j ≠ left (left (left t)) ∧
          gc.moverAt j ≠ left (left t) ∧
          gc.moverAt j ≠ left t)
    push_neg at hgood
    have hk_mem : k ∈ badSet := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ k, ?_⟩
      simp [badSet, hk_ge, hk_lt, hgood]
    have hne : badSet.Nonempty := ⟨k, hk_mem⟩
    obtain ⟨j, hj_mem, hj_min⟩ := Finset.exists_min_image badSet Fin.val hne
    have hj_ge : a0.val ≤ j.val := by
      simp [badSet] at hj_mem
      exact hj_mem.1
    have hj_lt : j.val < phase.s.val := by
      simp [badSet] at hj_mem
      exact hj_mem.2.1
    have hj_bad :
        ¬(gc.moverAt j = left (left (left t)) ∨
          gc.moverAt j = left (left t) ∨
          gc.moverAt j = left t) := by
      simp [badSet] at hj_mem
      rcases hj_mem.2.2 with ⟨hj3, hj2, hj1⟩
      intro h
      rcases h with h | h | h
      · exact hj3 h
      · exact hj2 h
      · exact hj1 h
    have hj_ne_a0 : j ≠ a0 := by
      intro hEq
      apply hj_bad
      left
      simpa [hEq] using ha0_left3
    have hj_gt : a0.val < j.val := by
      have hneq : j.val ≠ a0.val := by
        intro hval
        exact hj_ne_a0 (Fin.ext hval)
      omega
    let prev : Fin gc.configs.length := ⟨j.val - 1, by omega⟩
    have hprev_lt_j : prev.val < j.val := by
      dsimp [prev]
      omega
    have hprev_ge : a0.val ≤ prev.val := by
      dsimp [prev]
      omega
    have hprev_lt_s : prev.val < phase.s.val := by
      dsimp [prev]
      omega
    have hprev_not_mem : prev ∉ badSet := by
      intro hmem
      have := hj_min prev hmem
      exact False.elim (by omega)
    have hprev_good :
        gc.moverAt prev = left (left (left t)) ∨
        gc.moverAt prev = left (left t) ∨
        gc.moverAt prev = left t := by
      by_cases hprev_good :
          gc.moverAt prev = left (left (left t)) ∨
          gc.moverAt prev = left (left t) ∨
          gc.moverAt prev = left t
      · exact hprev_good
      · exfalso
        push_neg at hprev_good
        exact hprev_not_mem (by
          refine Finset.mem_filter.mpr ?_
          refine ⟨Finset.mem_univ prev, ?_⟩
          simp [badSet, hprev_ge, hprev_lt_s, hprev_good])
    have hj_ge_a : phase.a.val ≤ j.val := by omega
    have hj_nonmover : gc.moverAt j ≠ t := phase.ht_nofire j hj_ge_a hj_lt
    have hnext_eq : nextIndex gc.configs prev = j := by
      apply Fin.ext
      have hsucc : prev.val + 1 = j.val := by
        dsimp [prev]
        omega
      simp [nextIndex, prev, hsucc, Nat.mod_eq_of_lt j.isLt]
    have hnext_local := gc.next_mover_is_local prev
    rw [hnext_eq] at hnext_local
    have hj_local6 :
        gc.moverAt j = left (left t) ∨
        gc.moverAt j = left t ∨
        gc.moverAt j = right t ∨
        gc.moverAt j = right (right t) ∨
        gc.moverAt j = right (right (right t)) := by
      rcases htail6 j hj_gt hj_lt with hj3 | hjll | hjl | hjr | hjrr | hjr3
      · exact False.elim (hj_bad (Or.inl hj3))
      · exact Or.inl hjll
      · exact Or.inr (Or.inl hjl)
      · exact Or.inr (Or.inr (Or.inl hjr))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hjrr)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hjr3)))
    have hj_good :
        gc.moverAt j = left (left (left t)) ∨
        gc.moverAt j = left (left t) ∨
        gc.moverAt j = left t := by
      rcases hprev_good with hprev3 | hprev2 | hprev1
      · rcases hnext_local with hleft | hself | hright
        · exfalso
          have hj_l4 : gc.moverAt j = left (left (left (left t))) := by
            simpa [hprev3] using hleft
          apply left4_not_rightsix hn t
          rcases hj_local6 with hjll | hjl | hjr | hjrr | hjr3
          · exact Or.inl (by rw [← hj_l4, hjll])
          · exact Or.inr (Or.inl (by rw [← hj_l4, hjl]))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hj_l4, hjr]))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hj_l4, hjrr])))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [← hj_l4, hjr3])))))
        · exact Or.inl (by simpa [hprev3] using hself)
        · exact Or.inr (Or.inl (by simpa [hprev3] using hright))
      · rcases hnext_local with hleft | hself | hright
        · exact Or.inl (by simpa [hprev2] using hleft)
        · exact Or.inr (Or.inl (by simpa [hprev2] using hself))
        · exact Or.inr (Or.inr (by simpa [hprev2] using hright))
      · rcases hnext_local with hleft | hself | hright
        · exact Or.inr (Or.inl (by simpa [hprev1] using hleft))
        · exact Or.inr (Or.inr (by simpa [hprev1] using hself))
        · exfalso
          exact hj_nonmover (by simpa [hprev1] using hright)
    exact False.elim (hj_bad hj_good)

/-- Strengthened phase-tail right invariance: repeated `right^3(t)` steps are
    allowed in the phase tail. If the tail stays inside the pivot's
    6-neighborhood before the final `t`-fire, then it still remains entirely
    on the right side. -/
theorem phase_tail_from_right3_stays_right6
    (gc : GoodCycle sys) (t : Fin sys.rs.n) (phase : TernaryPhase gc t)
    (hn : sys.rs.n ≥ 8)
    (a0 : Fin gc.configs.length)
    (ha0_ge_a : phase.a.val ≤ a0.val)
    (ha0_lt_s : a0.val < phase.s.val)
    (ha0_right3 : gc.moverAt a0 = right (right (right t)))
    (htail6 : ∀ k : Fin gc.configs.length,
      a0.val < k.val → k.val < phase.s.val →
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t))) :
    ∀ k : Fin gc.configs.length,
      a0.val ≤ k.val → k.val < phase.s.val →
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t)) := by
  intro k hk_ge hk_lt
  by_cases hgood :
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t))
  · exact hgood
  · let badSet : Finset (Fin gc.configs.length) :=
      (Finset.univ : Finset (Fin gc.configs.length)).filter
        (fun j =>
          a0.val ≤ j.val ∧ j.val < phase.s.val ∧
          gc.moverAt j ≠ right t ∧
          gc.moverAt j ≠ right (right t) ∧
          gc.moverAt j ≠ right (right (right t)))
    push_neg at hgood
    have hk_mem : k ∈ badSet := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ k, ?_⟩
      simp [badSet, hk_ge, hk_lt, hgood]
    have hne : badSet.Nonempty := ⟨k, hk_mem⟩
    obtain ⟨j, hj_mem, hj_min⟩ := Finset.exists_min_image badSet Fin.val hne
    have hj_ge : a0.val ≤ j.val := by
      simp [badSet] at hj_mem
      exact hj_mem.1
    have hj_lt : j.val < phase.s.val := by
      simp [badSet] at hj_mem
      exact hj_mem.2.1
    have hj_bad :
        ¬(gc.moverAt j = right t ∨
          gc.moverAt j = right (right t) ∨
          gc.moverAt j = right (right (right t))) := by
      simp [badSet] at hj_mem
      rcases hj_mem.2.2 with ⟨hj1, hj2, hj3⟩
      intro h
      rcases h with h | h | h
      · exact hj1 h
      · exact hj2 h
      · exact hj3 h
    have hj_ne_a0 : j ≠ a0 := by
      intro hEq
      apply hj_bad
      exact Or.inr (Or.inr (by simpa [hEq] using ha0_right3))
    have hj_gt : a0.val < j.val := by
      have hneq : j.val ≠ a0.val := by
        intro hval
        exact hj_ne_a0 (Fin.ext hval)
      omega
    let prev : Fin gc.configs.length := ⟨j.val - 1, by omega⟩
    have hprev_lt_j : prev.val < j.val := by
      dsimp [prev]
      omega
    have hprev_ge : a0.val ≤ prev.val := by
      dsimp [prev]
      omega
    have hprev_lt_s : prev.val < phase.s.val := by
      dsimp [prev]
      omega
    have hprev_not_mem : prev ∉ badSet := by
      intro hmem
      have := hj_min prev hmem
      exact False.elim (by omega)
    have hprev_good :
        gc.moverAt prev = right t ∨
        gc.moverAt prev = right (right t) ∨
        gc.moverAt prev = right (right (right t)) := by
      by_cases hprev_good :
          gc.moverAt prev = right t ∨
          gc.moverAt prev = right (right t) ∨
          gc.moverAt prev = right (right (right t))
      · exact hprev_good
      · exfalso
        push_neg at hprev_good
        exact hprev_not_mem (by
          refine Finset.mem_filter.mpr ?_
          refine ⟨Finset.mem_univ prev, ?_⟩
          simp [badSet, hprev_ge, hprev_lt_s, hprev_good])
    have hj_ge_a : phase.a.val ≤ j.val := by omega
    have hj_nonmover : gc.moverAt j ≠ t := phase.ht_nofire j hj_ge_a hj_lt
    have hnext_eq : nextIndex gc.configs prev = j := by
      apply Fin.ext
      have hsucc : prev.val + 1 = j.val := by
        dsimp [prev]
        omega
      simp [nextIndex, prev, hsucc, Nat.mod_eq_of_lt j.isLt]
    have hnext_local := gc.next_mover_is_local prev
    rw [hnext_eq] at hnext_local
    have hj_local6 :
        gc.moverAt j = left (left (left t)) ∨
        gc.moverAt j = left (left t) ∨
        gc.moverAt j = left t ∨
        gc.moverAt j = right t ∨
        gc.moverAt j = right (right t) ∨
        gc.moverAt j = right (right (right t)) := by
      rcases htail6 j hj_gt hj_lt with hjl3 | hjll | hjl | hjr | hjrr | hjr3
      · exact Or.inl hjl3
      · exact Or.inr (Or.inl hjll)
      · exact Or.inr (Or.inr (Or.inl hjl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hjr)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hjrr))))
      · exact False.elim (hj_bad (Or.inr (Or.inr hjr3)))
    have hj_good :
        gc.moverAt j = right t ∨
        gc.moverAt j = right (right t) ∨
        gc.moverAt j = right (right (right t)) := by
      rcases hprev_good with hprev1 | hprev2 | hprev3
      · rcases hnext_local with hleft | hself | hright
        · exfalso
          exact hj_nonmover (by simpa [hprev1] using hleft)
        · exact Or.inl (by simpa [hprev1] using hself)
        · exact Or.inr (Or.inl (by simpa [hprev1] using hright))
      · rcases hnext_local with hleft | hself | hright
        · exact Or.inl (by simpa [hprev2] using hleft)
        · exact Or.inr (Or.inl (by simpa [hprev2] using hself))
        · exact Or.inr (Or.inr (by simpa [hprev2] using hright))
      · rcases hnext_local with hleft | hself | hright
        · exact Or.inr (Or.inl (by simpa [hprev3] using hleft))
        · exact Or.inr (Or.inr (by simpa [hprev3] using hself))
        · exfalso
          have hj_r4 : gc.moverAt j = right (right (right (right t))) := by
            simpa [hprev3] using hright
          rcases hj_local6 with hjl3 | hjll | hjl | hjr | hjrr | hjr3
          · exact False.elim (right4_not_leftsix hn t (Or.inl (by rw [← hj_r4, hjl3])))
          · exact False.elim (right4_not_leftsix hn t (Or.inr (Or.inl (by rw [← hj_r4, hjll]))))
          · exact False.elim (right4_not_leftsix hn t (Or.inr (Or.inr (Or.inl (by rw [← hj_r4, hjl])))))
          · exact False.elim (right4_not_leftsix hn t
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hj_r4, hjr])))))))
          · exact False.elim (right4_not_leftsix hn t
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [← hj_r4, hjrr])))))))
          · exact False.elim (right4_ne_right3 hn t (by rw [← hj_r4, hjr3]))
    exact False.elim (hj_bad hj_good)

/-- Strengthened phase-tail packaging: repeated `left^3(t)` / `right^3(t)`
    steps are allowed before the phase tail settles on one side. -/
theorem last_outside_phase_tail_one_sided6
    (gc : GoodCycle sys) (t : Fin sys.rs.n) (phase : TernaryPhase gc t)
    (hn : sys.rs.n ≥ 8)
    (a0 : Fin gc.configs.length)
    (ha0_ge_a : phase.a.val ≤ a0.val)
    (ha0_lt_s : a0.val < phase.s.val)
    (ha0_side :
      gc.moverAt a0 = left (left (left t)) ∨
      gc.moverAt a0 = right (right (right t)))
    (htail6 : ∀ k : Fin gc.configs.length,
      a0.val < k.val → k.val < phase.s.val →
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t))) :
    (∀ k : Fin gc.configs.length,
      a0.val ≤ k.val → k.val < phase.s.val →
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t) ∨
    (∀ k : Fin gc.configs.length,
      a0.val ≤ k.val → k.val < phase.s.val →
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t))) := by
  rcases ha0_side with ha0_left | ha0_right
  · exact Or.inl (phase_tail_from_left3_stays_left6 gc t phase hn a0
      ha0_ge_a ha0_lt_s ha0_left htail6)
  · exact Or.inr (phase_tail_from_right3_stays_right6 gc t phase hn a0
      ha0_ge_a ha0_lt_s ha0_right htail6)

/-- Terminal-tail variant of `phase_tail_from_left3_stays_left`: once the
    mover is at `left^3(t)`, all later movers stay in the pivot's local
    5-neighborhood, and `t` never fires again, the entire remaining suffix is
    forced to stay on the left side. -/
private theorem terminal_tail_from_left3_stays_left
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn : sys.rs.n ≥ 8)
    (a0 : Fin gc.configs.length)
    (ha0_left3 : gc.moverAt a0 = left (left (left t)))
    (htail_no_t : ∀ k : Fin gc.configs.length, a0.val ≤ k.val → gc.moverAt k ≠ t)
    (htail5 : ∀ k : Fin gc.configs.length,
      a0.val < k.val →
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t)) :
    ∀ k : Fin gc.configs.length,
      a0.val ≤ k.val →
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t := by
  intro k hk_ge
  by_cases hgood :
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t
  · exact hgood
  · let badSet : Finset (Fin gc.configs.length) :=
      (Finset.univ : Finset (Fin gc.configs.length)).filter
        (fun j =>
          a0.val ≤ j.val ∧
          gc.moverAt j ≠ left (left (left t)) ∧
          gc.moverAt j ≠ left (left t) ∧
          gc.moverAt j ≠ left t)
    push_neg at hgood
    have hk_mem : k ∈ badSet := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ k, ?_⟩
      simp [badSet, hk_ge, hgood]
    have hne : badSet.Nonempty := ⟨k, hk_mem⟩
    obtain ⟨j, hj_mem, hj_min⟩ := Finset.exists_min_image badSet Fin.val hne
    have hj_ge : a0.val ≤ j.val := by
      simp [badSet] at hj_mem
      exact hj_mem.1
    have hj_bad :
        ¬(gc.moverAt j = left (left (left t)) ∨
          gc.moverAt j = left (left t) ∨
          gc.moverAt j = left t) := by
      simp [badSet] at hj_mem
      rcases hj_mem.2 with ⟨hj3, hj2, hj1⟩
      intro h
      rcases h with h | h | h
      · exact hj3 h
      · exact hj2 h
      · exact hj1 h
    have hj_ne_a0 : j ≠ a0 := by
      intro hEq
      apply hj_bad
      left
      simpa [hEq] using ha0_left3
    have hj_gt : a0.val < j.val := by
      have hneq : j.val ≠ a0.val := by
        intro hval
        exact hj_ne_a0 (Fin.ext hval)
      omega
    let prev : Fin gc.configs.length := ⟨j.val - 1, by omega⟩
    have hprev_ge : a0.val ≤ prev.val := by
      dsimp [prev]
      omega
    have hprev_not_mem : prev ∉ badSet := by
      intro hmem
      have hle := hj_min prev hmem
      have : j.val ≤ j.val - 1 := by
        simpa [prev] using hle
      omega
    have hprev_good :
        gc.moverAt prev = left (left (left t)) ∨
        gc.moverAt prev = left (left t) ∨
        gc.moverAt prev = left t := by
      by_cases hprev_good :
          gc.moverAt prev = left (left (left t)) ∨
          gc.moverAt prev = left (left t) ∨
          gc.moverAt prev = left t
      · exact hprev_good
      · exfalso
        push_neg at hprev_good
        exact hprev_not_mem (by
          refine Finset.mem_filter.mpr ?_
          refine ⟨Finset.mem_univ prev, ?_⟩
          simp [badSet, hprev_ge, hprev_good])
    have hj_nonmover : gc.moverAt j ≠ t := htail_no_t j hj_ge
    have hnext_eq : nextIndex gc.configs prev = j := by
      apply Fin.ext
      have hsucc : prev.val + 1 = j.val := by
        dsimp [prev]
        omega
      simp [nextIndex, prev, hsucc, Nat.mod_eq_of_lt j.isLt]
    have hnext_local := gc.next_mover_is_local prev
    rw [hnext_eq] at hnext_local
    have hj_local5 :
        gc.moverAt j = left (left t) ∨
        gc.moverAt j = left t ∨
        gc.moverAt j = right t ∨
        gc.moverAt j = right (right t) := by
      exact htail5 j hj_gt
    have hj_good :
        gc.moverAt j = left (left (left t)) ∨
        gc.moverAt j = left (left t) ∨
        gc.moverAt j = left t := by
      rcases hprev_good with hprev3 | hprev2 | hprev1
      · rcases hnext_local with hleft | hself | hright
        · exfalso
          have hj_l4 : gc.moverAt j = left (left (left (left t))) := by
            simpa [hprev3] using hleft
          apply left4_not_local5 hn t
          rcases hj_local5 with hjll | hjl | hjr | hjrr
          · exact Or.inl (by rw [← hj_l4, hjll])
          · exact Or.inr (Or.inl (by rw [← hj_l4, hjl]))
          · exact Or.inr (Or.inr (Or.inl (by rw [← hj_l4, hjr])))
          · exact Or.inr (Or.inr (Or.inr (by rw [← hj_l4, hjrr])))
        · exfalso
          have hj_l3 : gc.moverAt j = left (left (left t)) := by
            simpa [hprev3] using hself
          apply left3_not_local5 hn t
          rcases hj_local5 with hjll | hjl | hjr | hjrr
          · exact Or.inl (by rw [← hj_l3, hjll])
          · exact Or.inr (Or.inl (by rw [← hj_l3, hjl]))
          · exact Or.inr (Or.inr (Or.inl (by rw [← hj_l3, hjr])))
          · exact Or.inr (Or.inr (Or.inr (by rw [← hj_l3, hjrr])))
        · exact Or.inr (Or.inl (by simpa [hprev3] using hright))
      · rcases hnext_local with hleft | hself | hright
        · exfalso
          have hj_l3 : gc.moverAt j = left (left (left t)) := by
            simpa [hprev2] using hleft
          apply left3_not_local5 hn t
          rcases hj_local5 with hjll | hjl | hjr | hjrr
          · exact Or.inl (by rw [← hj_l3, hjll])
          · exact Or.inr (Or.inl (by rw [← hj_l3, hjl]))
          · exact Or.inr (Or.inr (Or.inl (by rw [← hj_l3, hjr])))
          · exact Or.inr (Or.inr (Or.inr (by rw [← hj_l3, hjrr])))
        · exact Or.inr (Or.inl (by simpa [hprev2] using hself))
        · exact Or.inr (Or.inr (by simpa [hprev2] using hright))
      · rcases hnext_local with hleft | hself | hright
        · exact Or.inr (Or.inl (by simpa [hprev1] using hleft))
        · exact Or.inr (Or.inr (by simpa [hprev1] using hself))
        · exfalso
          exact hj_nonmover (by simpa [hprev1] using hright)
    exact False.elim (hj_bad hj_good)

/-- Symmetric no-`t` terminal-tail invariance lemma. -/
private theorem terminal_tail_from_right3_stays_right
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn : sys.rs.n ≥ 8)
    (a0 : Fin gc.configs.length)
    (ha0_right3 : gc.moverAt a0 = right (right (right t)))
    (htail_no_t : ∀ k : Fin gc.configs.length, a0.val ≤ k.val → gc.moverAt k ≠ t)
    (htail5 : ∀ k : Fin gc.configs.length,
      a0.val < k.val →
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t)) :
    ∀ k : Fin gc.configs.length,
      a0.val ≤ k.val →
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t)) := by
  intro k hk_ge
  by_cases hgood :
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t))
  · exact hgood
  · let badSet : Finset (Fin gc.configs.length) :=
      (Finset.univ : Finset (Fin gc.configs.length)).filter
        (fun j =>
          a0.val ≤ j.val ∧
          gc.moverAt j ≠ right t ∧
          gc.moverAt j ≠ right (right t) ∧
          gc.moverAt j ≠ right (right (right t)))
    push_neg at hgood
    have hk_mem : k ∈ badSet := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ k, ?_⟩
      simp [badSet, hk_ge, hgood]
    have hne : badSet.Nonempty := ⟨k, hk_mem⟩
    obtain ⟨j, hj_mem, hj_min⟩ := Finset.exists_min_image badSet Fin.val hne
    have hj_ge : a0.val ≤ j.val := by
      simp [badSet] at hj_mem
      exact hj_mem.1
    have hj_bad :
        ¬(gc.moverAt j = right t ∨
          gc.moverAt j = right (right t) ∨
          gc.moverAt j = right (right (right t))) := by
      simp [badSet] at hj_mem
      rcases hj_mem.2 with ⟨hj1, hj2, hj3⟩
      intro h
      rcases h with h | h | h
      · exact hj1 h
      · exact hj2 h
      · exact hj3 h
    have hj_ne_a0 : j ≠ a0 := by
      intro hEq
      apply hj_bad
      exact Or.inr (Or.inr (by simpa [hEq] using ha0_right3))
    have hj_gt : a0.val < j.val := by
      have hneq : j.val ≠ a0.val := by
        intro hval
        exact hj_ne_a0 (Fin.ext hval)
      omega
    let prev : Fin gc.configs.length := ⟨j.val - 1, by omega⟩
    have hprev_ge : a0.val ≤ prev.val := by
      dsimp [prev]
      omega
    have hprev_not_mem : prev ∉ badSet := by
      intro hmem
      have hle := hj_min prev hmem
      have : j.val ≤ j.val - 1 := by
        simpa [prev] using hle
      omega
    have hprev_good :
        gc.moverAt prev = right t ∨
        gc.moverAt prev = right (right t) ∨
        gc.moverAt prev = right (right (right t)) := by
      by_cases hprev_good :
          gc.moverAt prev = right t ∨
          gc.moverAt prev = right (right t) ∨
          gc.moverAt prev = right (right (right t))
      · exact hprev_good
      · exfalso
        push_neg at hprev_good
        exact hprev_not_mem (by
          refine Finset.mem_filter.mpr ?_
          refine ⟨Finset.mem_univ prev, ?_⟩
          simp [badSet, hprev_ge, hprev_good])
    have hj_nonmover : gc.moverAt j ≠ t := htail_no_t j hj_ge
    have hnext_eq : nextIndex gc.configs prev = j := by
      apply Fin.ext
      have hsucc : prev.val + 1 = j.val := by
        dsimp [prev]
        omega
      simp [nextIndex, prev, hsucc, Nat.mod_eq_of_lt j.isLt]
    have hnext_local := gc.next_mover_is_local prev
    rw [hnext_eq] at hnext_local
    have hj_local5 :
        gc.moverAt j = left (left t) ∨
        gc.moverAt j = left t ∨
        gc.moverAt j = right t ∨
        gc.moverAt j = right (right t) := by
      exact htail5 j hj_gt
    have hj_good :
        gc.moverAt j = right t ∨
        gc.moverAt j = right (right t) ∨
        gc.moverAt j = right (right (right t)) := by
      rcases hprev_good with hprev1 | hprev2 | hprev3
      · rcases hnext_local with hleft | hself | hright
        · exfalso
          exact hj_nonmover (by simpa [hprev1] using hleft)
        · exact Or.inl (by simpa [hprev1] using hself)
        · exact Or.inr (Or.inl (by simpa [hprev1] using hright))
      · rcases hnext_local with hleft | hself | hright
        · exact Or.inl (by simpa [hprev2] using hleft)
        · exact Or.inr (Or.inl (by simpa [hprev2] using hself))
        · exfalso
          have hj_r3 : gc.moverAt j = right (right (right t)) := by
            simpa [hprev2] using hright
          apply right3_not_local5 hn t
          rcases hj_local5 with hjll | hjl | hjr | hjrr
          · exact Or.inl (by rw [← hj_r3, hjll])
          · exact Or.inr (Or.inl (by rw [← hj_r3, hjl]))
          · exact Or.inr (Or.inr (Or.inl (by rw [← hj_r3, hjr])))
          · exact Or.inr (Or.inr (Or.inr (by rw [← hj_r3, hjrr])))
      · rcases hnext_local with hleft | hself | hright
        · exact Or.inr (Or.inl (by simpa [hprev3] using hleft))
        · exfalso
          have hj_r3 : gc.moverAt j = right (right (right t)) := by
            simpa [hprev3] using hself
          apply right3_not_local5 hn t
          rcases hj_local5 with hjll | hjl | hjr | hjrr
          · exact Or.inl (by rw [← hj_r3, hjll])
          · exact Or.inr (Or.inl (by rw [← hj_r3, hjl]))
          · exact Or.inr (Or.inr (Or.inl (by rw [← hj_r3, hjr])))
          · exact Or.inr (Or.inr (Or.inr (by rw [← hj_r3, hjrr])))
        · exfalso
          have hj_r4 : gc.moverAt j = right (right (right (right t))) := by
            simpa [hprev3] using hright
          apply right4_not_local5 hn t
          rcases hj_local5 with hjll | hjl | hjr | hjrr
          · exact Or.inl (by rw [← hj_r4, hjll])
          · exact Or.inr (Or.inl (by rw [← hj_r4, hjl]))
          · exact Or.inr (Or.inr (Or.inl (by rw [← hj_r4, hjr])))
          · exact Or.inr (Or.inr (Or.inr (by rw [← hj_r4, hjrr])))
    exact False.elim (hj_bad hj_good)

/-- Terminal no-`t` tail packaging: after the last outside mover, if `t` never
    fires again and all later movers are local to the pivot, then the whole
    terminal tail is one-sided. -/
private theorem last_outside_terminal_tail_one_sided
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn : sys.rs.n ≥ 8)
    (a0 : Fin gc.configs.length)
    (ha0_side :
      gc.moverAt a0 = left (left (left t)) ∨
      gc.moverAt a0 = right (right (right t)))
    (htail_no_t : ∀ k : Fin gc.configs.length, a0.val ≤ k.val → gc.moverAt k ≠ t)
    (htail5 : ∀ k : Fin gc.configs.length,
      a0.val < k.val →
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t)) :
    (∀ k : Fin gc.configs.length,
      a0.val ≤ k.val →
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t) ∨
    (∀ k : Fin gc.configs.length,
      a0.val ≤ k.val →
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t))) := by
  rcases ha0_side with ha0_left | ha0_right
  · exact Or.inl (terminal_tail_from_left3_stays_left gc t hn a0
      ha0_left htail_no_t htail5)
  · exact Or.inr (terminal_tail_from_right3_stays_right gc t hn a0
      ha0_right htail_no_t htail5)

/-- Strengthened terminal-tail left invariance: repeated `left^3(t)` steps are
    allowed in the tail. If the tail stays inside the pivot's 6-neighborhood
    and never fires `t`, then it still remains entirely on the left side. -/
private theorem terminal_tail_from_left3_stays_left6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn : sys.rs.n ≥ 8)
    (a0 : Fin gc.configs.length)
    (ha0_left3 : gc.moverAt a0 = left (left (left t)))
    (htail_no_t : ∀ k : Fin gc.configs.length, a0.val ≤ k.val → gc.moverAt k ≠ t)
    (htail6 : ∀ k : Fin gc.configs.length,
      a0.val < k.val →
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t))) :
    ∀ k : Fin gc.configs.length,
      a0.val ≤ k.val →
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t := by
  intro k hk_ge
  by_cases hgood :
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t
  · exact hgood
  · let badSet : Finset (Fin gc.configs.length) :=
      (Finset.univ : Finset (Fin gc.configs.length)).filter
        (fun j =>
          a0.val ≤ j.val ∧
          gc.moverAt j ≠ left (left (left t)) ∧
          gc.moverAt j ≠ left (left t) ∧
          gc.moverAt j ≠ left t)
    push_neg at hgood
    have hk_mem : k ∈ badSet := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ k, ?_⟩
      simp [badSet, hk_ge, hgood]
    have hne : badSet.Nonempty := ⟨k, hk_mem⟩
    obtain ⟨j, hj_mem, hj_min⟩ := Finset.exists_min_image badSet Fin.val hne
    have hj_ge : a0.val ≤ j.val := by
      simp [badSet] at hj_mem
      exact hj_mem.1
    have hj_bad :
        ¬(gc.moverAt j = left (left (left t)) ∨
          gc.moverAt j = left (left t) ∨
          gc.moverAt j = left t) := by
      simp [badSet] at hj_mem
      rcases hj_mem.2 with ⟨hj3, hj2, hj1⟩
      intro h
      rcases h with h | h | h
      · exact hj3 h
      · exact hj2 h
      · exact hj1 h
    have hj_ne_a0 : j ≠ a0 := by
      intro hEq
      apply hj_bad
      left
      simpa [hEq] using ha0_left3
    have hj_gt : a0.val < j.val := by
      have hneq : j.val ≠ a0.val := by
        intro hval
        exact hj_ne_a0 (Fin.ext hval)
      omega
    let prev : Fin gc.configs.length := ⟨j.val - 1, by omega⟩
    have hprev_ge : a0.val ≤ prev.val := by
      dsimp [prev]
      omega
    have hprev_not_mem : prev ∉ badSet := by
      intro hmem
      have hle := hj_min prev hmem
      have : j.val ≤ j.val - 1 := by
        simpa [prev] using hle
      omega
    have hprev_good :
        gc.moverAt prev = left (left (left t)) ∨
        gc.moverAt prev = left (left t) ∨
        gc.moverAt prev = left t := by
      by_cases hprev_good :
          gc.moverAt prev = left (left (left t)) ∨
          gc.moverAt prev = left (left t) ∨
          gc.moverAt prev = left t
      · exact hprev_good
      · exfalso
        push_neg at hprev_good
        exact hprev_not_mem (by
          refine Finset.mem_filter.mpr ?_
          refine ⟨Finset.mem_univ prev, ?_⟩
          simp [badSet, hprev_ge, hprev_good])
    have hj_nonmover : gc.moverAt j ≠ t := htail_no_t j hj_ge
    have hnext_eq : nextIndex gc.configs prev = j := by
      apply Fin.ext
      have hsucc : prev.val + 1 = j.val := by
        dsimp [prev]
        omega
      simp [nextIndex, prev, hsucc, Nat.mod_eq_of_lt j.isLt]
    have hnext_local := gc.next_mover_is_local prev
    rw [hnext_eq] at hnext_local
    have hj_local6 :
        gc.moverAt j = left (left t) ∨
        gc.moverAt j = left t ∨
        gc.moverAt j = right t ∨
        gc.moverAt j = right (right t) ∨
        gc.moverAt j = right (right (right t)) := by
      rcases htail6 j hj_gt with hj3 | hjll | hjl | hjr | hjrr | hjr3
      · exact False.elim (hj_bad (Or.inl hj3))
      · exact Or.inl hjll
      · exact Or.inr (Or.inl hjl)
      · exact Or.inr (Or.inr (Or.inl hjr))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hjrr)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hjr3)))
    have hj_good :
        gc.moverAt j = left (left (left t)) ∨
        gc.moverAt j = left (left t) ∨
        gc.moverAt j = left t := by
      rcases hprev_good with hprev3 | hprev2 | hprev1
      · rcases hnext_local with hleft | hself | hright
        · exfalso
          have hj_l4 : gc.moverAt j = left (left (left (left t))) := by
            simpa [hprev3] using hleft
          apply left4_not_rightsix hn t
          rcases hj_local6 with hjll | hjl | hjr | hjrr | hjr3
          · exact Or.inl (by rw [← hj_l4, hjll])
          · exact Or.inr (Or.inl (by rw [← hj_l4, hjl]))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hj_l4, hjr]))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hj_l4, hjrr])))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [← hj_l4, hjr3])))))
        · exact Or.inl (by simpa [hprev3] using hself)
        · exact Or.inr (Or.inl (by simpa [hprev3] using hright))
      · rcases hnext_local with hleft | hself | hright
        · exact Or.inl (by simpa [hprev2] using hleft)
        · exact Or.inr (Or.inl (by simpa [hprev2] using hself))
        · exact Or.inr (Or.inr (by simpa [hprev2] using hright))
      · rcases hnext_local with hleft | hself | hright
        · exact Or.inr (Or.inl (by simpa [hprev1] using hleft))
        · exact Or.inr (Or.inr (by simpa [hprev1] using hself))
        · exfalso
          exact hj_nonmover (by simpa [hprev1] using hright)
    exact False.elim (hj_bad hj_good)

/-- Strengthened terminal-tail right invariance: repeated `right^3(t)` steps are
    allowed in the tail. If the tail stays inside the pivot's 6-neighborhood
    and never fires `t`, then it still remains entirely on the right side. -/
private theorem terminal_tail_from_right3_stays_right6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn : sys.rs.n ≥ 8)
    (a0 : Fin gc.configs.length)
    (ha0_right3 : gc.moverAt a0 = right (right (right t)))
    (htail_no_t : ∀ k : Fin gc.configs.length, a0.val ≤ k.val → gc.moverAt k ≠ t)
    (htail6 : ∀ k : Fin gc.configs.length,
      a0.val < k.val →
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t))) :
    ∀ k : Fin gc.configs.length,
      a0.val ≤ k.val →
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t)) := by
  intro k hk_ge
  by_cases hgood :
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t))
  · exact hgood
  · let badSet : Finset (Fin gc.configs.length) :=
      (Finset.univ : Finset (Fin gc.configs.length)).filter
        (fun j =>
          a0.val ≤ j.val ∧
          gc.moverAt j ≠ right t ∧
          gc.moverAt j ≠ right (right t) ∧
          gc.moverAt j ≠ right (right (right t)))
    push_neg at hgood
    have hk_mem : k ∈ badSet := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ k, ?_⟩
      simp [badSet, hk_ge, hgood]
    have hne : badSet.Nonempty := ⟨k, hk_mem⟩
    obtain ⟨j, hj_mem, hj_min⟩ := Finset.exists_min_image badSet Fin.val hne
    have hj_ge : a0.val ≤ j.val := by
      simp [badSet] at hj_mem
      exact hj_mem.1
    have hj_bad :
        ¬(gc.moverAt j = right t ∨
          gc.moverAt j = right (right t) ∨
          gc.moverAt j = right (right (right t))) := by
      simp [badSet] at hj_mem
      rcases hj_mem.2 with ⟨hj1, hj2, hj3⟩
      intro h
      rcases h with h | h | h
      · exact hj1 h
      · exact hj2 h
      · exact hj3 h
    have hj_ne_a0 : j ≠ a0 := by
      intro hEq
      apply hj_bad
      exact Or.inr (Or.inr (by simpa [hEq] using ha0_right3))
    have hj_gt : a0.val < j.val := by
      have hneq : j.val ≠ a0.val := by
        intro hval
        exact hj_ne_a0 (Fin.ext hval)
      omega
    let prev : Fin gc.configs.length := ⟨j.val - 1, by omega⟩
    have hprev_ge : a0.val ≤ prev.val := by
      dsimp [prev]
      omega
    have hprev_not_mem : prev ∉ badSet := by
      intro hmem
      have hle := hj_min prev hmem
      have : j.val ≤ j.val - 1 := by
        simpa [prev] using hle
      omega
    have hprev_good :
        gc.moverAt prev = right t ∨
        gc.moverAt prev = right (right t) ∨
        gc.moverAt prev = right (right (right t)) := by
      by_cases hprev_good :
          gc.moverAt prev = right t ∨
          gc.moverAt prev = right (right t) ∨
          gc.moverAt prev = right (right (right t))
      · exact hprev_good
      · exfalso
        push_neg at hprev_good
        exact hprev_not_mem (by
          refine Finset.mem_filter.mpr ?_
          refine ⟨Finset.mem_univ prev, ?_⟩
          simp [badSet, hprev_ge, hprev_good])
    have hj_nonmover : gc.moverAt j ≠ t := htail_no_t j hj_ge
    have hnext_eq : nextIndex gc.configs prev = j := by
      apply Fin.ext
      have hsucc : prev.val + 1 = j.val := by
        dsimp [prev]
        omega
      simp [nextIndex, prev, hsucc, Nat.mod_eq_of_lt j.isLt]
    have hnext_local := gc.next_mover_is_local prev
    rw [hnext_eq] at hnext_local
    have hj_local6 :
        gc.moverAt j = left (left (left t)) ∨
        gc.moverAt j = left (left t) ∨
        gc.moverAt j = left t ∨
        gc.moverAt j = right t ∨
        gc.moverAt j = right (right t) ∨
        gc.moverAt j = right (right (right t)) := by
      rcases htail6 j hj_gt with hjl3 | hjll | hjl | hjr | hjrr | hjr3
      · exact Or.inl hjl3
      · exact Or.inr (Or.inl hjll)
      · exact Or.inr (Or.inr (Or.inl hjl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hjr)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hjrr))))
      · exact False.elim (hj_bad (Or.inr (Or.inr hjr3)))
    have hj_good :
        gc.moverAt j = right t ∨
        gc.moverAt j = right (right t) ∨
        gc.moverAt j = right (right (right t)) := by
      rcases hprev_good with hprev1 | hprev2 | hprev3
      · rcases hnext_local with hleft | hself | hright
        · exfalso
          exact hj_nonmover (by simpa [hprev1] using hleft)
        · exact Or.inl (by simpa [hprev1] using hself)
        · exact Or.inr (Or.inl (by simpa [hprev1] using hright))
      · rcases hnext_local with hleft | hself | hright
        · exact Or.inl (by simpa [hprev2] using hleft)
        · exact Or.inr (Or.inl (by simpa [hprev2] using hself))
        · exact Or.inr (Or.inr (by simpa [hprev2] using hright))
      · rcases hnext_local with hleft | hself | hright
        · exact Or.inr (Or.inl (by simpa [hprev3] using hleft))
        · exact Or.inr (Or.inr (by simpa [hprev3] using hself))
        · exfalso
          have hj_r4 : gc.moverAt j = right (right (right (right t))) := by
            simpa [hprev3] using hright
          rcases hj_local6 with hjl3 | hjll | hjl | hjr | hjrr | hjr3
          · exact False.elim (right4_not_leftsix hn t (Or.inl (by rw [← hj_r4, hjl3])))
          · exact False.elim (right4_not_leftsix hn t (Or.inr (Or.inl (by rw [← hj_r4, hjll]))))
          · exact False.elim (right4_not_leftsix hn t (Or.inr (Or.inr (Or.inl (by rw [← hj_r4, hjl])))))
          · exact False.elim (right4_not_leftsix hn t
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hj_r4, hjr])))))))
          · exact False.elim (right4_not_leftsix hn t
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [← hj_r4, hjrr])))))))
          · exact False.elim (right4_ne_right3 hn t (by rw [← hj_r4, hjr3]))
    exact False.elim (hj_bad hj_good)

/-- Strengthened terminal-tail packaging: repeated `left^3(t)` / `right^3(t)`
    steps are allowed before the terminal suffix settles on one side. -/
theorem last_outside_terminal_tail_one_sided6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn : sys.rs.n ≥ 8)
    (a0 : Fin gc.configs.length)
    (ha0_side :
      gc.moverAt a0 = left (left (left t)) ∨
      gc.moverAt a0 = right (right (right t)))
    (htail_no_t : ∀ k : Fin gc.configs.length, a0.val ≤ k.val → gc.moverAt k ≠ t)
    (htail6 : ∀ k : Fin gc.configs.length,
      a0.val < k.val →
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t))) :
    (∀ k : Fin gc.configs.length,
      a0.val ≤ k.val →
      gc.moverAt k = left (left (left t)) ∨
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t) ∨
    (∀ k : Fin gc.configs.length,
      a0.val ≤ k.val →
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t) ∨
      gc.moverAt k = right (right (right t))) := by
  rcases ha0_side with ha0_left | ha0_right
  · exact Or.inl (terminal_tail_from_left3_stays_left6 gc t hn a0
      ha0_left htail_no_t htail6)
  · exact Or.inr (terminal_tail_from_right3_stays_right6 gc t hn a0
      ha0_right htail_no_t htail6)

/-- In a left-biased 6-tail, if we start at `right^2(t)` and later reach
    `left^3(t)`, then there is an interior edge `left^2(t) -> left^3(t)`. -/
theorem first_left3_after_right2_in_leftsix_tail
    (gc : GoodCycle sys) (t : Fin sys.rs.n) (hn : sys.rs.n ≥ 8)
    (j j1 k_out : Fin gc.configs.length)
    (hj_lt_j1 : j.val < j1.val)
    (hj1_lt_kout : j1.val < k_out.val)
    (hj1_right2 : gc.moverAt j1 = right (right t))
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t)) :
    ∃ a prev : Fin gc.configs.length,
      j1.val ≤ prev.val ∧
      prev.val + 1 = a.val ∧
      a.val ≤ k_out.val ∧
      gc.moverAt prev = left (left t) ∧
      gc.moverAt a = left (left (left t)) := by
  let left3Set : Finset (Fin gc.configs.length) :=
    (Finset.univ : Finset (Fin gc.configs.length)).filter
      (fun a => j1.val < a.val ∧ gc.moverAt a = left (left (left t)))
  have hkout_mem : k_out ∈ left3Set := by
    refine Finset.mem_filter.mpr ?_
    exact ⟨Finset.mem_univ k_out, hj1_lt_kout, hkout_left3⟩
  obtain ⟨a, ha_mem, ha_min⟩ :=
    Finset.exists_min_image left3Set Fin.val ⟨k_out, hkout_mem⟩
  have ha_gt_j1 : j1.val < a.val := by
    simp [left3Set] at ha_mem
    exact ha_mem.1
  have ha_left3 : gc.moverAt a = left (left (left t)) := by
    simp [left3Set] at ha_mem
    exact ha_mem.2
  have ha_le_kout : a.val ≤ k_out.val := by
    exact ha_min k_out hkout_mem
  have hprev_lt : a.val - 1 < gc.configs.length := by omega
  let prev : Fin gc.configs.length := ⟨a.val - 1, hprev_lt⟩
  have hprev_succ : prev.val + 1 = a.val := by
    dsimp [prev]
    omega
  have hprev_gt_j : j.val < prev.val := by
    dsimp [prev]
    omega
  have hprev_local6 := hj_tail prev hprev_gt_j
  have hnext_eq : nextIndex gc.configs prev = a := by
    apply Fin.ext
    simp [nextIndex, prev, hprev_succ]
    exact Nat.mod_eq_of_lt a.isLt
  have hnext_local := gc.next_mover_is_local prev
  rw [hnext_eq] at hnext_local
  have hprev_ne_left3 : gc.moverAt prev ≠ left (left (left t)) := by
    intro hprev_eq
    by_cases hEq : prev = j1
    · apply right2_ne_left3 hn t
      rw [hEq] at hprev_eq
      exact Eq.trans hj1_right2.symm hprev_eq
    · have hprev_lt_a : prev.val < a.val := by
        dsimp [prev]
        omega
      have hprev_mem : prev ∈ left3Set := by
        refine Finset.mem_filter.mpr ?_
        exact ⟨Finset.mem_univ prev, by
          dsimp [prev]
          omega, hprev_eq⟩
      have hle := ha_min prev hprev_mem
      have : a.val ≤ prev.val := by simpa using hle
      omega
  have hprev_left2 : gc.moverAt prev = left (left t) := by
    rcases hnext_local with hleft | hself | hright
    · have htmp : left (left t) = gc.moverAt prev := by
        simpa [ha_left3, right_left_eq_self] using congrArg right hleft
      exact htmp.symm
    · exact False.elim (hprev_ne_left3 (by simpa [ha_left3] using hself.symm))
    · exfalso
      have hprev_left4 : gc.moverAt prev = left (left (left (left t))) := by
        have htmp : left (left (left (left t))) = gc.moverAt prev := by
          simpa [ha_left3, left_right_eq_self] using congrArg left hright
        exact htmp.symm
      apply left4_not_leftsix hn t
      rcases hprev_local6 with h | h | h | h | h | h
      · exact Or.inl (by rw [← hprev_left4, h])
      · exact Or.inr (Or.inl (by rw [← hprev_left4, h]))
      · exact Or.inr (Or.inr (Or.inl (by rw [← hprev_left4, h])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hprev_left4, h]))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hprev_left4, h])))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [← hprev_left4, h])))))
  refine ⟨a, prev, ?_, hprev_succ, ha_le_kout, hprev_left2, ha_left3⟩
  dsimp [prev]
  omega

/-- In a right-biased 6-tail, if we start at `left^2(t)` and later reach
    `right^3(t)`, then there is an interior edge `right^2(t) -> right^3(t)`. -/
theorem first_right3_after_left2_in_rightsix_tail
    (gc : GoodCycle sys) (t : Fin sys.rs.n) (hn : sys.rs.n ≥ 8)
    (j j1 k_out : Fin gc.configs.length)
    (hj_lt_j1 : j.val < j1.val)
    (hj1_lt_kout : j1.val < k_out.val)
    (hj1_left2 : gc.moverAt j1 = left (left t))
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t))) :
    ∃ a prev : Fin gc.configs.length,
      j1.val ≤ prev.val ∧
      prev.val + 1 = a.val ∧
      a.val ≤ k_out.val ∧
      gc.moverAt prev = right (right t) ∧
      gc.moverAt a = right (right (right t)) := by
  let right3Set : Finset (Fin gc.configs.length) :=
    (Finset.univ : Finset (Fin gc.configs.length)).filter
      (fun a => j1.val < a.val ∧ gc.moverAt a = right (right (right t)))
  have hkout_mem : k_out ∈ right3Set := by
    refine Finset.mem_filter.mpr ?_
    exact ⟨Finset.mem_univ k_out, hj1_lt_kout, hkout_right3⟩
  obtain ⟨a, ha_mem, ha_min⟩ :=
    Finset.exists_min_image right3Set Fin.val ⟨k_out, hkout_mem⟩
  have ha_gt_j1 : j1.val < a.val := by
    simp [right3Set] at ha_mem
    exact ha_mem.1
  have ha_right3 : gc.moverAt a = right (right (right t)) := by
    simp [right3Set] at ha_mem
    exact ha_mem.2
  have ha_le_kout : a.val ≤ k_out.val := by
    exact ha_min k_out hkout_mem
  have hprev_lt : a.val - 1 < gc.configs.length := by omega
  let prev : Fin gc.configs.length := ⟨a.val - 1, hprev_lt⟩
  have hprev_succ : prev.val + 1 = a.val := by
    dsimp [prev]
    omega
  have hprev_gt_j : j.val < prev.val := by
    dsimp [prev]
    omega
  have hprev_local6 := hj_tail prev hprev_gt_j
  have hnext_eq : nextIndex gc.configs prev = a := by
    apply Fin.ext
    simp [nextIndex, prev, hprev_succ]
    exact Nat.mod_eq_of_lt a.isLt
  have hnext_local := gc.next_mover_is_local prev
  rw [hnext_eq] at hnext_local
  have hprev_ne_right3 : gc.moverAt prev ≠ right (right (right t)) := by
    intro hprev_eq
    by_cases hEq : prev = j1
    · apply left2_ne_right3 hn t
      rw [hEq] at hprev_eq
      exact Eq.trans hj1_left2.symm hprev_eq
    · have hprev_lt_a : prev.val < a.val := by
        dsimp [prev]
        omega
      have hprev_mem : prev ∈ right3Set := by
        refine Finset.mem_filter.mpr ?_
        exact ⟨Finset.mem_univ prev, by
          dsimp [prev]
          omega, hprev_eq⟩
      have hle := ha_min prev hprev_mem
      have : a.val ≤ prev.val := by simpa using hle
      omega
  have hprev_right2 : gc.moverAt prev = right (right t) := by
    rcases hnext_local with hleft | hself | hright
    · exfalso
      have hprev_right4 : gc.moverAt prev = right (right (right (right t))) := by
        have htmp : right (right (right (right t))) = gc.moverAt prev := by
          simpa [ha_right3, right_left_eq_self] using congrArg right hleft
        exact htmp.symm
      apply right4_not_rightsix hn t
      rcases hprev_local6 with h | h | h | h | h | h
      · exact Or.inl (by rw [← hprev_right4, h])
      · exact Or.inr (Or.inl (by rw [← hprev_right4, h]))
      · exact Or.inr (Or.inr (Or.inl (by rw [← hprev_right4, h])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hprev_right4, h]))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hprev_right4, h])))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [← hprev_right4, h])))))
    · exact False.elim (hprev_ne_right3 (by simpa [ha_right3] using hself.symm))
    · have htmp : right (right t) = gc.moverAt prev := by
        simpa [ha_right3, left_right_eq_self] using congrArg left hright
      exact htmp.symm
  refine ⟨a, prev, ?_, hprev_succ, ha_le_kout, hprev_right2, ha_right3⟩
  dsimp [prev]
  omega

/-- In a left-biased 6-tail, if we start at `left^2(t)` and later reach
    `left^3(t)`, then there is an interior edge `left^2(t) -> left^3(t)`. -/
theorem first_left3_after_left2_in_leftsix_tail
    (gc : GoodCycle sys) (t : Fin sys.rs.n) (hn : sys.rs.n ≥ 8)
    (j a0 k_out : Fin gc.configs.length)
    (hj_lt_a0 : j.val < a0.val)
    (ha0_lt_kout : a0.val < k_out.val)
    (ha0_left2 : gc.moverAt a0 = left (left t))
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t)) :
    ∃ a prev : Fin gc.configs.length,
      a0.val ≤ prev.val ∧
      prev.val + 1 = a.val ∧
      a.val ≤ k_out.val ∧
      gc.moverAt prev = left (left t) ∧
      gc.moverAt a = left (left (left t)) := by
  let left3Set : Finset (Fin gc.configs.length) :=
    (Finset.univ : Finset (Fin gc.configs.length)).filter
      (fun a => a0.val < a.val ∧ gc.moverAt a = left (left (left t)))
  have hkout_mem : k_out ∈ left3Set := by
    refine Finset.mem_filter.mpr ?_
    exact ⟨Finset.mem_univ k_out, ha0_lt_kout, hkout_left3⟩
  obtain ⟨a, ha_mem, ha_min⟩ :=
    Finset.exists_min_image left3Set Fin.val ⟨k_out, hkout_mem⟩
  have ha_gt_a0 : a0.val < a.val := by
    simp [left3Set] at ha_mem
    exact ha_mem.1
  have ha_left3 : gc.moverAt a = left (left (left t)) := by
    simp [left3Set] at ha_mem
    exact ha_mem.2
  have ha_le_kout : a.val ≤ k_out.val := by
    exact ha_min k_out hkout_mem
  have hprev_lt : a.val - 1 < gc.configs.length := by omega
  let prev : Fin gc.configs.length := ⟨a.val - 1, hprev_lt⟩
  have hprev_succ : prev.val + 1 = a.val := by
    dsimp [prev]
    omega
  have hprev_gt_j : j.val < prev.val := by
    dsimp [prev]
    omega
  have hprev_local6 := hj_tail prev hprev_gt_j
  have hnext_eq : nextIndex gc.configs prev = a := by
    apply Fin.ext
    simp [nextIndex, prev, hprev_succ]
    exact Nat.mod_eq_of_lt a.isLt
  have hnext_local := gc.next_mover_is_local prev
  rw [hnext_eq] at hnext_local
  have hprev_ne_left3 : gc.moverAt prev ≠ left (left (left t)) := by
    intro hprev_eq
    by_cases hEq : prev = a0
    · exact (left3_not_local5 hn t) (Or.inl (by
        calc
          left (left (left t)) = gc.moverAt prev := hprev_eq.symm
          _ = gc.moverAt a0 := by rw [hEq]
          _ = left (left t) := ha0_left2))
    · have hprev_mem : prev ∈ left3Set := by
        refine Finset.mem_filter.mpr ?_
        exact ⟨Finset.mem_univ prev, by
          dsimp [prev]
          omega, hprev_eq⟩
      have hle := ha_min prev hprev_mem
      have : a.val ≤ prev.val := by simpa using hle
      omega
  have hprev_left2 : gc.moverAt prev = left (left t) := by
    rcases hnext_local with hleft | hself | hright
    · have htmp : left (left t) = gc.moverAt prev := by
        simpa [ha_left3, right_left_eq_self] using congrArg right hleft
      exact htmp.symm
    · exact False.elim (hprev_ne_left3 (by simpa [ha_left3] using hself.symm))
    · exfalso
      have hprev_left4 : gc.moverAt prev = left (left (left (left t))) := by
        have htmp : left (left (left (left t))) = gc.moverAt prev := by
          simpa [ha_left3, left_right_eq_self] using congrArg left hright
        exact htmp.symm
      apply left4_not_leftsix hn t
      rcases hprev_local6 with h | h | h | h | h | h
      · exact Or.inl (by rw [← hprev_left4, h])
      · exact Or.inr (Or.inl (by rw [← hprev_left4, h]))
      · exact Or.inr (Or.inr (Or.inl (by rw [← hprev_left4, h])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hprev_left4, h]))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hprev_left4, h])))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [← hprev_left4, h])))))
  refine ⟨a, prev, ?_, hprev_succ, ha_le_kout, hprev_left2, ha_left3⟩
  dsimp [prev]
  omega

/-- In a right-biased 6-tail, if we start at `right^2(t)` and later reach
    `right^3(t)`, then there is an interior edge `right^2(t) -> right^3(t)`. -/
theorem first_right3_after_right2_in_rightsix_tail
    (gc : GoodCycle sys) (t : Fin sys.rs.n) (hn : sys.rs.n ≥ 8)
    (j a0 k_out : Fin gc.configs.length)
    (hj_lt_a0 : j.val < a0.val)
    (ha0_lt_kout : a0.val < k_out.val)
    (ha0_right2 : gc.moverAt a0 = right (right t))
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t))) :
    ∃ a prev : Fin gc.configs.length,
      a0.val ≤ prev.val ∧
      prev.val + 1 = a.val ∧
      a.val ≤ k_out.val ∧
      gc.moverAt prev = right (right t) ∧
      gc.moverAt a = right (right (right t)) := by
  let right3Set : Finset (Fin gc.configs.length) :=
    (Finset.univ : Finset (Fin gc.configs.length)).filter
      (fun a => a0.val < a.val ∧ gc.moverAt a = right (right (right t)))
  have hkout_mem : k_out ∈ right3Set := by
    refine Finset.mem_filter.mpr ?_
    exact ⟨Finset.mem_univ k_out, ha0_lt_kout, hkout_right3⟩
  obtain ⟨a, ha_mem, ha_min⟩ :=
    Finset.exists_min_image right3Set Fin.val ⟨k_out, hkout_mem⟩
  have ha_gt_a0 : a0.val < a.val := by
    simp [right3Set] at ha_mem
    exact ha_mem.1
  have ha_right3 : gc.moverAt a = right (right (right t)) := by
    simp [right3Set] at ha_mem
    exact ha_mem.2
  have ha_le_kout : a.val ≤ k_out.val := by
    exact ha_min k_out hkout_mem
  have hprev_lt : a.val - 1 < gc.configs.length := by omega
  let prev : Fin gc.configs.length := ⟨a.val - 1, hprev_lt⟩
  have hprev_succ : prev.val + 1 = a.val := by
    dsimp [prev]
    omega
  have hprev_gt_j : j.val < prev.val := by
    dsimp [prev]
    omega
  have hprev_local6 := hj_tail prev hprev_gt_j
  have hnext_eq : nextIndex gc.configs prev = a := by
    apply Fin.ext
    simp [nextIndex, prev, hprev_succ]
    exact Nat.mod_eq_of_lt a.isLt
  have hnext_local := gc.next_mover_is_local prev
  rw [hnext_eq] at hnext_local
  have hprev_ne_right3 : gc.moverAt prev ≠ right (right (right t)) := by
    intro hprev_eq
    by_cases hEq : prev = a0
    · exact (right3_not_local5 hn t) (Or.inr (Or.inr (Or.inr (by
        calc
          right (right (right t)) = gc.moverAt prev := hprev_eq.symm
          _ = gc.moverAt a0 := by rw [hEq]
          _ = right (right t) := ha0_right2))))
    · have hprev_mem : prev ∈ right3Set := by
        refine Finset.mem_filter.mpr ?_
        exact ⟨Finset.mem_univ prev, by
          dsimp [prev]
          omega, hprev_eq⟩
      have hle := ha_min prev hprev_mem
      have : a.val ≤ prev.val := by simpa using hle
      omega
  have hprev_right2 : gc.moverAt prev = right (right t) := by
    rcases hnext_local with hleft | hself | hright
    · exfalso
      have hprev_right4 : gc.moverAt prev = right (right (right (right t))) := by
        have htmp : right (right (right (right t))) = gc.moverAt prev := by
          simpa [ha_right3, right_left_eq_self] using congrArg right hleft
        exact htmp.symm
      apply right4_not_rightsix hn t
      rcases hprev_local6 with h | h | h | h | h | h
      · exact Or.inl (by rw [← hprev_right4, h])
      · exact Or.inr (Or.inl (by rw [← hprev_right4, h]))
      · exact Or.inr (Or.inr (Or.inl (by rw [← hprev_right4, h])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hprev_right4, h]))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hprev_right4, h])))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [← hprev_right4, h])))))
    · exact False.elim (hprev_ne_right3 (by simpa [ha_right3] using hself.symm))
    · have htmp : right (right t) = gc.moverAt prev := by
        simpa [ha_right3, left_right_eq_self] using congrArg left hright
      exact htmp.symm
  refine ⟨a, prev, ?_, hprev_succ, ha_le_kout, hprev_right2, ha_right3⟩
  dsimp [prev]
  omega

/-- If `k_out` is a globally last outside mover for the pivot `t` and `t`
    never fires again after `k_out`, then the remaining terminal suffix is
    either trivial (`k_out` is the last step) or entirely one-sided. -/
theorem last_outside_no_t_suffix_one_sided_or_last
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn : sys.rs.n ≥ 8)
    (k_out : Fin gc.configs.length)
    (hk_outside :
      gc.moverAt k_out ≠ left (left t) ∧
      gc.moverAt k_out ≠ left t ∧
      gc.moverAt k_out ≠ t ∧
      gc.moverAt k_out ≠ right t ∧
      gc.moverAt k_out ≠ right (right t))
    (hk_out_last :
      ∀ k : Fin gc.configs.length,
        k_out.val < k.val →
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t ∨
        gc.moverAt k = t ∨
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t))
    (hno_t_after : ∀ k : Fin gc.configs.length, k_out.val < k.val → gc.moverAt k ≠ t) :
    (k_out.val + 1 = gc.configs.length) ∨
    ((∀ k : Fin gc.configs.length,
        k_out.val ≤ k.val →
        gc.moverAt k = left (left (left t)) ∨
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t) ∨
     (∀ k : Fin gc.configs.length,
        k_out.val ≤ k.val →
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t) ∨
        gc.moverAt k = right (right (right t)))) := by
  by_cases hk_last : k_out.val + 1 = gc.configs.length
  · exact Or.inl hk_last
  · have hk1_lt : k_out.val + 1 < gc.configs.length := by omega
    let a1 : Fin gc.configs.length := ⟨k_out.val + 1, hk1_lt⟩
    have ha1_eq_next : nextIndex gc.configs k_out = a1 := by
      apply Fin.ext
      simp [nextIndex, a1]
      exact Nat.mod_eq_of_lt hk1_lt
    have ha1_local :
        gc.moverAt a1 = left (left t) ∨
        gc.moverAt a1 = left t ∨
        gc.moverAt a1 = t ∨
        gc.moverAt a1 = right t ∨
        gc.moverAt a1 = right (right t) := by
      exact hk_out_last a1 (by
        dsimp [a1]
        omega)
    have ha1_local5 :
        gc.moverAt a1 = left (left t) ∨
        gc.moverAt a1 = left t ∨
        gc.moverAt a1 = right t ∨
        gc.moverAt a1 = right (right t) := by
      rcases ha1_local with ha1ll | ha1l | ha1t | ha1r | ha1rr
      · exact Or.inl ha1ll
      · exact Or.inr (Or.inl ha1l)
      · exfalso
        exact hno_t_after a1 (by
          dsimp [a1]
          omega) ha1t
      · exact Or.inr (Or.inr (Or.inl ha1r))
      · exact Or.inr (Or.inr (Or.inr ha1rr))
    have hside :
        gc.moverAt k_out = left (left (left t)) ∨
        gc.moverAt k_out = right (right (right t)) :=
      outside_step_followed_by_local_five_forces_side gc t k_out a1
        ha1_eq_next hk_outside
        (by
          rcases ha1_local5 with ha1ll | ha1l | ha1r | ha1rr
          · exact Or.inl ha1ll
          · exact Or.inr (Or.inl ha1l)
          · exact Or.inr (Or.inr (Or.inr (Or.inl ha1r)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr ha1rr))))
    have htail_no_t : ∀ k : Fin gc.configs.length, k_out.val ≤ k.val → gc.moverAt k ≠ t := by
      intro k hk_ge
      by_cases hk_eq : k = k_out
      · subst hk_eq
        exact hk_outside.2.2.1
      · have hk_gt : k_out.val < k.val := by
          have hneq_val : k.val ≠ k_out.val := by
            intro hval
            exact hk_eq (Fin.ext hval)
          omega
        exact hno_t_after k hk_gt
    have htail5 :
        ∀ k : Fin gc.configs.length,
          k_out.val < k.val →
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) := by
      intro k hk_gt
      rcases hk_out_last k hk_gt with hkll | hkl | hkt | hkr | hkrr
      · exact Or.inl hkll
      · exact Or.inr (Or.inl hkl)
      · exfalso
        exact hno_t_after k hk_gt hkt
      · exact Or.inr (Or.inr (Or.inl hkr))
      · exact Or.inr (Or.inr (Or.inr hkrr))
    exact Or.inr (last_outside_terminal_tail_one_sided gc t hn k_out
      hside htail_no_t htail5)

/-- Symmetric discrete IVT: f(m) ≤ v ≤ f(0).
    Proved by applying discrete_ivt to the reversed sequence g(i) = f(m - i). -/
private theorem discrete_ivt_sym (m : Nat) (f : Nat → Nat)
    (hup : ∀ k, k < m → f (k + 1) ≤ f k + 1)
    (hdn : ∀ k, k < m → f k ≤ f (k + 1) + 1)
    (v : Nat) (hlo : f m ≤ v) (hhi : v ≤ f 0) :
    ∃ k, k ≤ m ∧ f k = v := by
  -- Apply discrete_ivt to g(i) = f(m - i)
  set g : Nat → Nat := fun i => f (m - i)
  have hg0 : g 0 = f m := by simp [g]
  have hgm : g m = f 0 := by simp [g]
  have hg_up : ∀ k, k < m → g (k + 1) ≤ g k + 1 := by
    intro k hk; simp [g]
    -- g(k+1) = f(m - k - 1), g(k) = f(m - k)
    -- Need: f(m-k-1) ≤ f(m-k) + 1
    -- This is hdn applied to (m-k-1): f(m-k-1) ≤ f(m-k-1+1) + 1 = f(m-k) + 1
    have := hdn (m - k - 1) (by omega)
    rw [show m - k - 1 + 1 = m - k by omega] at this
    exact this
  have hg_dn : ∀ k, k < m → g k ≤ g (k + 1) + 1 := by
    intro k hk; simp [g]
    have := hup (m - k - 1) (by omega)
    rw [show m - k - 1 + 1 = m - k by omega] at this
    exact this
  obtain ⟨k, hk, hgk⟩ := discrete_ivt m g hg_up hg_dn v (by rw [hg0]; exact hlo)
    (by rw [hgm]; exact hhi)
  refine ⟨m - k, by omega, ?_⟩
  simp [g] at hgk; exact hgk

/-- Walk visits all cwShift values between any two visited values.
    Key sub-lemma for firingSupport_connected_arc.
    Proved using discrete_ivt + cwShift_right_step/cwShift_left_step. -/
private theorem walk_visits_between' (gc : GoodCycle sys)
    (i₀ : Fin sys.rs.n) (hfc0 : gc.fireCount i₀ = 0)
    (j₁ j₂ : Fin gc.configs.length) (v : Nat)
    (hv_lo : min (cwShift i₀ (gc.moverAt j₁)) (cwShift i₀ (gc.moverAt j₂)) ≤ v)
    (hv_hi : v ≤ max (cwShift i₀ (gc.moverAt j₁)) (cwShift i₀ (gc.moverAt j₂))) :
    ∃ k : Fin gc.configs.length, cwShift i₀ (gc.moverAt k) = v := by
  have hN4 : sys.rs.n ≥ 4 := sys.rs.n_ge_4
  have hne_i₀ : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ i₀ :=
    moverAt_ne_of_fc_zero gc i₀ hfc0
  -- cwShift of any mover is < n - 1 (since mover ≠ i₀)
  have hcw_lt : ∀ k : Fin gc.configs.length, cwShift i₀ (gc.moverAt k) < sys.rs.n - 1 := by
    intro k
    have hlt := cwShift_lt (show sys.rs.n ≥ 1 by omega) i₀ (gc.moverAt k)
    by_contra h; push_neg at h
    exact hne_i₀ k ((cwShift_eq_pred_iff hN4 i₀ (gc.moverAt k)).mp (by omega))
  -- Step property: cwShift changes by at most 1 along the walk
  have hstep_up : ∀ k : Fin gc.configs.length,
      cwShift i₀ (gc.moverAt (nextIndex gc.configs k)) ≤
      cwShift i₀ (gc.moverAt k) + 1 := by
    intro k
    rcases gc.next_mover_is_local k with hleft | hself | hright
    · -- next = left(current): cwShift decreases by 1 or wraps
      rw [hleft]
      by_cases hpos : 0 < cwShift i₀ (gc.moverAt k)
      · rw [cwShift_left_step hN4 i₀ (gc.moverAt k) hpos]; omega
      · -- cwShift = 0 means current = right(i₀), left(current) = i₀
        -- But next mover ≠ i₀, contradiction
        exfalso; apply hne_i₀ (nextIndex gc.configs k)
        rw [hleft]
        have : cwShift i₀ (gc.moverAt k) = 0 := by omega
        have : gc.moverAt k = right i₀ := (cwShift_eq_zero_iff hN4 i₀ _).mp this
        rw [this, left_right_eq_self]
    · -- next = self: cwShift unchanged
      rw [hself]; omega
    · -- next = right(current): cwShift increases by 1
      rw [hright, cwShift_right_step hN4 i₀ (gc.moverAt k) (hcw_lt k)]
  have hstep_dn : ∀ k : Fin gc.configs.length,
      cwShift i₀ (gc.moverAt k) ≤
      cwShift i₀ (gc.moverAt (nextIndex gc.configs k)) + 1 := by
    intro k
    rcases gc.next_mover_is_local k with hleft | hself | hright
    · rw [hleft]
      by_cases hpos : 0 < cwShift i₀ (gc.moverAt k)
      · rw [cwShift_left_step hN4 i₀ (gc.moverAt k) hpos]; omega
      · exfalso; apply hne_i₀ (nextIndex gc.configs k)
        rw [hleft]
        have : cwShift i₀ (gc.moverAt k) = 0 := by omega
        have : gc.moverAt k = right i₀ := (cwShift_eq_zero_iff hN4 i₀ _).mp this
        rw [this, left_right_eq_self]
    · rw [hself]; omega
    · rw [hright, cwShift_right_step hN4 i₀ (gc.moverAt k) (hcw_lt k)]; omega
  -- Use WLOG: swap j₁ and j₂ if needed so cwShift(j₁) ≤ cwShift(j₂)
  -- Strategy: define walk along the cycle from j₁, apply discrete_ivt
  have hL_pos : 0 < gc.configs.length := gc.configs_length_pos
  -- Helper: iterate nextIndex k times from a starting point
  have iter_eq : ∀ (start : Fin gc.configs.length) (k : Nat),
      (⟨(start.val + k) % gc.configs.length, Nat.mod_lt _ hL_pos⟩ : Fin gc.configs.length) =
      Nat.iterate (nextIndex gc.configs) k start := by
    intro start k
    induction k with
    | zero => ext; simp [Nat.mod_eq_of_lt start.isLt]
    | succ k ih =>
      simp only [Function.iterate_succ', Function.comp]
      rw [← ih]; ext; simp only [nextIndex]
      show (start.val + (k + 1)) % gc.configs.length = ((start.val + k) % gc.configs.length + 1) % gc.configs.length
      -- (start + (k+1)) % L = ((start + k) % L + 1) % L
      by_cases h1 : gc.configs.length = 1
      · simp [h1, Nat.mod_one]
      · have h2 : gc.configs.length ≥ 2 := by omega
        rw [show start.val + (k + 1) = (start.val + k) + 1 from by ring,
          Nat.add_mod (start.val + k) 1 gc.configs.length,
          Nat.mod_eq_of_lt (by omega : 1 < gc.configs.length)]
  -- Step property along iterated walk
  have hstep_iter_up : ∀ (start : Fin gc.configs.length) (k : Nat),
      cwShift i₀ (gc.moverAt (Nat.iterate (nextIndex gc.configs) (k + 1) start)) ≤
      cwShift i₀ (gc.moverAt (Nat.iterate (nextIndex gc.configs) k start)) + 1 := by
    intro start k
    simp only [Function.iterate_succ', Function.comp]
    exact hstep_up _
  have hstep_iter_dn : ∀ (start : Fin gc.configs.length) (k : Nat),
      cwShift i₀ (gc.moverAt (Nat.iterate (nextIndex gc.configs) k start)) ≤
      cwShift i₀ (gc.moverAt (Nat.iterate (nextIndex gc.configs) (k + 1) start)) + 1 := by
    intro start k
    simp only [Function.iterate_succ', Function.comp]
    exact hstep_dn _
  -- Define walk from j₁
  set m₂ := (j₂.val + gc.configs.length - j₁.val) % gc.configs.length
  set f : Nat → Nat := fun k =>
    cwShift i₀ (gc.moverAt (Nat.iterate (nextIndex gc.configs) k j₁))
  have hf0 : f 0 = cwShift i₀ (gc.moverAt j₁) := by simp [f]
  have hiter_m₂ : Nat.iterate (nextIndex gc.configs) m₂ j₁ = j₂ := by
    rw [← iter_eq j₁ m₂]; ext
    show (j₁.val + (j₂.val + gc.configs.length - j₁.val) % gc.configs.length) % gc.configs.length = j₂.val
    have hj₂lt := j₂.isLt
    have hj₁lt := j₁.isLt
    by_cases h : j₂.val ≥ j₁.val
    · rw [show j₂.val + gc.configs.length - j₁.val = j₂.val - j₁.val + gc.configs.length by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : j₂.val - j₁.val < gc.configs.length),
        show j₁.val + (j₂.val - j₁.val) = j₂.val by omega,
        Nat.mod_eq_of_lt hj₂lt]
    · push_neg at h
      rw [Nat.mod_eq_of_lt (by omega : j₂.val + gc.configs.length - j₁.val < gc.configs.length),
        show j₁.val + (j₂.val + gc.configs.length - j₁.val) = j₂.val + gc.configs.length by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hj₂lt]
  have hfm₂ : f m₂ = cwShift i₀ (gc.moverAt j₂) := by
    simp only [f]; rw [hiter_m₂]
  have hf_up : ∀ k, k < m₂ → f (k + 1) ≤ f k + 1 := by
    intro k _; simp only [f]; exact hstep_iter_up j₁ k
  have hf_dn : ∀ k, k < m₂ → f k ≤ f (k + 1) + 1 := by
    intro k _; simp only [f]; exact hstep_iter_dn j₁ k
  -- Apply IVT based on direction
  by_cases hdir : cwShift i₀ (gc.moverAt j₁) ≤ cwShift i₀ (gc.moverAt j₂)
  · -- f(0) ≤ v ≤ f(m₂)
    have hlo : f 0 ≤ v := by
      rw [hf0]; rwa [min_eq_left hdir] at hv_lo
    have hhi : v ≤ f m₂ := by
      rw [hfm₂]; rwa [max_eq_right hdir] at hv_hi
    obtain ⟨k, _, hfk⟩ := discrete_ivt m₂ f hf_up hf_dn v hlo hhi
    exact ⟨Nat.iterate (nextIndex gc.configs) k j₁, hfk⟩
  · -- f(m₂) ≤ v ≤ f(0): walk from j₂ to j₁ instead
    push_neg at hdir
    -- Walk from j₂ instead
    set m₁ := (j₁.val + gc.configs.length - j₂.val) % gc.configs.length
    set g : Nat → Nat := fun k =>
      cwShift i₀ (gc.moverAt (Nat.iterate (nextIndex gc.configs) k j₂))
    have hg0 : g 0 = cwShift i₀ (gc.moverAt j₂) := by simp [g]
    have hiter_m₁ : Nat.iterate (nextIndex gc.configs) m₁ j₂ = j₁ := by
      rw [← iter_eq j₂ m₁]; ext
      show (j₂.val + (j₁.val + gc.configs.length - j₂.val) % gc.configs.length) % gc.configs.length = j₁.val
      have hj₂lt := j₂.isLt
      have hj₁lt := j₁.isLt
      by_cases h : j₁.val ≥ j₂.val
      · rw [show j₁.val + gc.configs.length - j₂.val = j₁.val - j₂.val + gc.configs.length by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : j₁.val - j₂.val < gc.configs.length),
          show j₂.val + (j₁.val - j₂.val) = j₁.val by omega,
          Nat.mod_eq_of_lt hj₁lt]
      · push_neg at h
        rw [Nat.mod_eq_of_lt (by omega : j₁.val + gc.configs.length - j₂.val < gc.configs.length),
          show j₂.val + (j₁.val + gc.configs.length - j₂.val) = j₁.val + gc.configs.length by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hj₁lt]
    have hgm₁ : g m₁ = cwShift i₀ (gc.moverAt j₁) := by
      simp only [g]; rw [hiter_m₁]
    have hg_up : ∀ k, k < m₁ → g (k + 1) ≤ g k + 1 := by
      intro k _; simp only [g]; exact hstep_iter_up j₂ k
    have hg_dn : ∀ k, k < m₁ → g k ≤ g (k + 1) + 1 := by
      intro k _; simp only [g]; exact hstep_iter_dn j₂ k
    have hlo : g 0 ≤ v := by
      rw [hg0]; rwa [min_eq_right (Nat.le_of_lt hdir)] at hv_lo
    have hhi : v ≤ g m₁ := by
      rw [hgm₁]; rwa [max_eq_left (Nat.le_of_lt hdir)] at hv_hi
    obtain ⟨k, _, hgk⟩ := discrete_ivt m₁ g hg_up hg_dn v hlo hhi
    exact ⟨Nat.iterate (nextIndex gc.configs) k j₂, hgk⟩

/-- **Mover walk connectivity implies |Z| ≥ 3 is impossible.**
    Proof via cwShift (CW displacement) + discrete IVT + domination.
    Pick i₀ ∈ Z, define d = cwShift i₀. Walk d-values ∈ [0,n-2].
    Find j₀ ∈ Z not adjacent to i₀, bracket d(j₀) between two visited
    d-values, apply IVT to show the walk visits j₀, contradicting fc(j₀) = 0. -/
private theorem firingSupport_connected_arc (gc : GoodCycle sys)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hn : sys.rs.n ≥ 9) :
    (zeroSet gc).card ≥ 3 →
    ∃ i : Fin sys.rs.n,
      gc.fireCount i = 0 ∧ gc.fireCount (right i) = 0 ∧
      gc.fireCount (right (right i)) = 0 := by
  intro hZ3
  exfalso
  have hN4 : sys.rs.n ≥ 4 := sys.rs.n_ge_4
  -- Pick i₀ ∈ Z
  obtain ⟨i₀, hi₀_mem⟩ := Finset.card_pos.mp (show 0 < (zeroSet gc).card by omega)
  have hfc0 : gc.fireCount i₀ = 0 := by simp [zeroSet] at hi₀_mem; exact hi₀_mem
  -- Walk avoids i₀
  have hne_i₀ : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ i₀ :=
    moverAt_ne_of_fc_zero gc i₀ hfc0
  -- Helper: extract step from positive fire count
  have step_of_fc_pos : ∀ q : Fin sys.rs.n, gc.fireCount q > 0 →
      ∃ k : Fin gc.configs.length, gc.moverAt k = q := by
    intro q hq; by_contra hall; push_neg at hall
    have : gc.fireCount q = 0 := by
      rw [gc.fireCount_eq_sum_moverAt]; apply Finset.sum_eq_zero
      intro j _; simp [hall j]
    omega
  -- From domination at i₀: right(i₀) or left(i₀) fires.
  have hdom_i₀ := firingSupport_dominates gc hno_safe i₀
  -- Case 1: right(i₀) fires (walk visits d = 0).
  by_cases hfc_ri₀ : gc.fireCount (right i₀) > 0
  · -- Pick j₀ ∈ Z, j₀ ∉ {i₀, left(i₀), right(i₀)}.
    -- right(i₀) fires so right(i₀) ∉ Z. Remove i₀ and left(i₀) from Z; ≥ 1 remains.
    obtain ⟨j₀, hfc_j₀, hj₀_ne_i₀, hj₀_ne_li₀, hj₀_ne_ri₀⟩ :
        ∃ j₀ : Fin sys.rs.n, gc.fireCount j₀ = 0 ∧
        j₀ ≠ i₀ ∧ j₀ ≠ left i₀ ∧ j₀ ≠ right i₀ := by
      -- right(i₀) ∉ zeroSet since it fires
      have hri_not_z : right i₀ ∉ zeroSet gc := by
        simp [zeroSet]; omega
      -- Remove i₀ from Z: card ≥ 2
      have hZ'_card : ((zeroSet gc).erase i₀).card ≥ 2 := by
        rw [Finset.card_erase_of_mem hi₀_mem]; omega
      -- Remove left(i₀) too: card ≥ 1
      have hZ''_card : (((zeroSet gc).erase i₀).erase (left i₀)).card ≥ 1 := by
        by_cases hleft_mem : left i₀ ∈ (zeroSet gc).erase i₀
        · rw [Finset.card_erase_of_mem hleft_mem]; omega
        · rw [Finset.erase_eq_of_notMem hleft_mem]; omega
      obtain ⟨j₀, hj₀_mem⟩ := Finset.card_pos.mp (by omega : 0 < (((zeroSet gc).erase i₀).erase (left i₀)).card)
      have hj₀_ne_li₀ : j₀ ≠ left i₀ := by
        intro heq; rw [heq] at hj₀_mem; exact (Finset.notMem_erase _ _) hj₀_mem
      have hj₀_in_erase : j₀ ∈ (zeroSet gc).erase i₀ :=
        Finset.mem_of_mem_erase hj₀_mem
      have hj₀_ne_i₀ : j₀ ≠ i₀ := by
        intro heq; rw [heq] at hj₀_in_erase; exact (Finset.notMem_erase _ _) hj₀_in_erase
      have hj₀_in_Z : j₀ ∈ zeroSet gc := Finset.mem_of_mem_erase hj₀_in_erase
      have hfc_j₀ : gc.fireCount j₀ = 0 := by simp [zeroSet] at hj₀_in_Z; exact hj₀_in_Z
      have hj₀_ne_ri₀ : j₀ ≠ right i₀ := by
        intro heq; rw [heq] at hj₀_in_Z; exact hri_not_z hj₀_in_Z
      exact ⟨j₀, hfc_j₀, hj₀_ne_i₀, hj₀_ne_li₀, hj₀_ne_ri₀⟩
    -- j₀ has d ∈ [1, n-3]
    have hd_j₀_pos : 0 < cwShift i₀ j₀ := by
      by_contra h; push_neg at h
      exact hj₀_ne_ri₀ ((cwShift_eq_zero_iff hN4 i₀ j₀).mp (by omega))
    have hd_j₀_lt : cwShift i₀ j₀ < sys.rs.n - 1 := by
      by_contra h; push_neg at h
      have := cwShift_lt (show sys.rs.n ≥ 1 by omega) i₀ j₀
      exact hj₀_ne_i₀ ((cwShift_eq_pred_iff hN4 i₀ j₀).mp (by omega))
    -- d(j₀) ≤ n-3: if d(j₀) = n-2, then right(j₀) = i₀, so j₀ = left(i₀), contradiction.
    have hd_j₀_lt2 : cwShift i₀ j₀ < sys.rs.n - 2 := by
      by_contra h; push_neg at h
      have heq : cwShift i₀ j₀ = sys.rs.n - 2 := by omega
      -- cwShift(right j₀) = cwShift(j₀) + 1 = n - 1, so right j₀ = i₀, j₀ = left i₀
      have := cwShift_right_step hN4 i₀ j₀ hd_j₀_lt
      rw [heq] at this
      have hrj_eq : right j₀ = i₀ := (cwShift_eq_pred_iff hN4 i₀ (right j₀)).mp (by omega)
      have := congrArg left hrj_eq
      rw [left_right_eq_self] at this
      exact hj₀_ne_li₀ this
    -- right(j₀) fires, or right(j₀) ∈ Z and right(right(j₀)) fires.
    -- Either way, ∃ firing proc q with cwShift i₀ q > cwShift i₀ j₀.
    obtain ⟨q, k_q, hk_q, hd_q_gt⟩ :
        ∃ (q : Fin sys.rs.n) (k_q : Fin gc.configs.length),
        gc.moverAt k_q = q ∧ cwShift i₀ q > cwShift i₀ j₀ := by
      by_cases hfc_rj₀ : gc.fireCount (right j₀) > 0
      · obtain ⟨k, hk⟩ := step_of_fc_pos _ hfc_rj₀
        exact ⟨_, k, hk, by rw [cwShift_right_step hN4 i₀ j₀ hd_j₀_lt]; omega⟩
      · have hfc_rj₀_eq : gc.fireCount (right j₀) = 0 := by omega
        have := no_three_consecutive_zeroFC gc hno_safe j₀ hfc_j₀ hfc_rj₀_eq
        obtain ⟨k, hk⟩ := step_of_fc_pos _ this
        have h1 : cwShift i₀ (right j₀) < sys.rs.n - 1 := by
          rw [cwShift_right_step hN4 i₀ j₀ hd_j₀_lt]; omega
        exact ⟨_, k, hk, by
          rw [cwShift_right_step hN4 i₀ (right j₀) h1,
            cwShift_right_step hN4 i₀ j₀ hd_j₀_lt]; omega⟩
    -- Walk visits d = 0 (right(i₀)) and d > d(j₀) (q). By IVT, visits d(j₀).
    obtain ⟨k_r, hk_r⟩ := step_of_fc_pos _ hfc_ri₀
    obtain ⟨k_hit, hk_hit⟩ := walk_visits_between' gc i₀ hfc0 k_r k_q
      (cwShift i₀ j₀)
      (by simp [hk_r, cwShift_right_self hN4 i₀])
      (by simp [hk_q]; omega)
    -- moverAt(k_hit) = j₀ (cwShift injective), contradicting fc(j₀) = 0.
    exact absurd (cwShift_injective hN4 i₀ hk_hit) (moverAt_ne_of_fc_zero gc j₀ hfc_j₀ k_hit)
  · -- Case 2: right(i₀) doesn't fire. left(i₀) fires. right(right(i₀)) fires.
    have hfc_ri₀_eq : gc.fireCount (right i₀) = 0 := by omega
    have hfc_li₀ : gc.fireCount (left i₀) > 0 := by
      rcases hdom_i₀ with h | h | h <;> omega
    have hfc_rri₀ := no_three_consecutive_zeroFC gc hno_safe i₀ hfc0 hfc_ri₀_eq
    obtain ⟨k_rr, hk_rr⟩ := step_of_fc_pos _ hfc_rri₀
    -- Walk visits d = 1 (right(right(i₀)))
    have hd_rr_eq : cwShift i₀ (gc.moverAt k_rr) = 1 := by
      rw [hk_rr, cwShift_right_step hN4 i₀ (right i₀) (by
        rw [cwShift_right_self hN4 i₀]; omega), cwShift_right_self hN4 i₀]
    -- Pick j₀ ∈ Z, j₀ ∉ {i₀, right(i₀), left(i₀)}. right(i₀) ∈ Z. left(i₀) ∉ Z.
    obtain ⟨j₀, hfc_j₀, hj₀_ne_i₀, hj₀_ne_li₀, hj₀_ne_ri₀⟩ :
        ∃ j₀ : Fin sys.rs.n, gc.fireCount j₀ = 0 ∧
        j₀ ≠ i₀ ∧ j₀ ≠ left i₀ ∧ j₀ ≠ right i₀ := by
      -- left(i₀) ∉ zeroSet since it fires
      have hli_not_z : left i₀ ∉ zeroSet gc := by
        simp [zeroSet]; omega
      -- right(i₀) ∈ zeroSet since it doesn't fire
      have hri_in_z : right i₀ ∈ zeroSet gc := by
        simp [zeroSet]; exact hfc_ri₀_eq
      -- Remove i₀ from Z: card ≥ 2
      have hZ'_card : ((zeroSet gc).erase i₀).card ≥ 2 := by
        rw [Finset.card_erase_of_mem hi₀_mem]; omega
      -- Remove right(i₀) too: card ≥ 1 (right(i₀) ∈ Z and right(i₀) ≠ i₀ since n ≥ 4)
      have hri_ne_i₀ : right i₀ ≠ i₀ := by
        intro heq
        have := congrArg Fin.val heq
        simp only [right_val] at this
        have hp := i₀.isLt
        by_cases hp1 : i₀.val + 1 < sys.rs.n
        · rw [Nat.mod_eq_of_lt hp1] at this; omega
        · rw [show i₀.val + 1 = sys.rs.n from by omega, Nat.mod_self] at this; omega
      have hri_in_erase : right i₀ ∈ (zeroSet gc).erase i₀ :=
        Finset.mem_erase.mpr ⟨hri_ne_i₀, hri_in_z⟩
      have hZ''_card : (((zeroSet gc).erase i₀).erase (right i₀)).card ≥ 1 := by
        rw [Finset.card_erase_of_mem hri_in_erase]; omega
      obtain ⟨j₀, hj₀_mem⟩ := Finset.card_pos.mp (by omega : 0 < (((zeroSet gc).erase i₀).erase (right i₀)).card)
      have hj₀_ne_ri₀ : j₀ ≠ right i₀ := by
        intro heq; rw [heq] at hj₀_mem; exact (Finset.notMem_erase _ _) hj₀_mem
      have hj₀_in_erase : j₀ ∈ (zeroSet gc).erase i₀ :=
        Finset.mem_of_mem_erase hj₀_mem
      have hj₀_ne_i₀ : j₀ ≠ i₀ := by
        intro heq; rw [heq] at hj₀_in_erase; exact (Finset.notMem_erase _ _) hj₀_in_erase
      have hj₀_in_Z : j₀ ∈ zeroSet gc := Finset.mem_of_mem_erase hj₀_in_erase
      have hfc_j₀ : gc.fireCount j₀ = 0 := by simp [zeroSet] at hj₀_in_Z; exact hj₀_in_Z
      have hj₀_ne_li₀ : j₀ ≠ left i₀ := by
        intro heq; rw [heq] at hj₀_in_Z; exact hli_not_z hj₀_in_Z
      exact ⟨j₀, hfc_j₀, hj₀_ne_i₀, hj₀_ne_li₀, hj₀_ne_ri₀⟩
    have hd_j₀_pos : 0 < cwShift i₀ j₀ := by
      by_contra h; push_neg at h
      exact hj₀_ne_ri₀ ((cwShift_eq_zero_iff hN4 i₀ j₀).mp (by omega))
    have hd_j₀_lt : cwShift i₀ j₀ < sys.rs.n - 1 := by
      by_contra h; push_neg at h
      have := cwShift_lt (show sys.rs.n ≥ 1 by omega) i₀ j₀
      exact hj₀_ne_i₀ ((cwShift_eq_pred_iff hN4 i₀ j₀).mp (by omega))
    have hd_j₀_lt2 : cwShift i₀ j₀ < sys.rs.n - 2 := by
      by_contra h; push_neg at h
      have heq : cwShift i₀ j₀ = sys.rs.n - 2 := by omega
      have := cwShift_right_step hN4 i₀ j₀ hd_j₀_lt
      rw [heq] at this
      have hrj_eq : right j₀ = i₀ := (cwShift_eq_pred_iff hN4 i₀ (right j₀)).mp (by omega)
      have := congrArg left hrj_eq
      rw [left_right_eq_self] at this
      exact hj₀_ne_li₀ this
    -- j₀ has d ≥ 2 (d = 1 is right(right(i₀)) which fires, but j₀ has fc = 0)
    have hd_j₀_gt1 : cwShift i₀ j₀ > 1 := by
      by_contra h; push_neg at h
      have : cwShift i₀ j₀ = 1 := by omega
      have hd_rri₀ : cwShift i₀ (right (right i₀)) = 1 := by
        rw [cwShift_right_step hN4 i₀ (right i₀) (by
          rw [cwShift_right_self hN4 i₀]; omega), cwShift_right_self hN4 i₀]
      rw [cwShift_injective hN4 i₀ (‹cwShift i₀ j₀ = 1›.trans hd_rri₀.symm)] at hfc_j₀; omega
    -- Get firing proc with d > d(j₀)
    obtain ⟨q, k_q, hk_q, hd_q_gt⟩ :
        ∃ (q : Fin sys.rs.n) (k_q : Fin gc.configs.length),
        gc.moverAt k_q = q ∧ cwShift i₀ q > cwShift i₀ j₀ := by
      by_cases hfc_rj₀ : gc.fireCount (right j₀) > 0
      · obtain ⟨k, hk⟩ := step_of_fc_pos _ hfc_rj₀
        exact ⟨_, k, hk, by rw [cwShift_right_step hN4 i₀ j₀ hd_j₀_lt]; omega⟩
      · have hfc_rj₀_eq : gc.fireCount (right j₀) = 0 := by omega
        have := no_three_consecutive_zeroFC gc hno_safe j₀ hfc_j₀ hfc_rj₀_eq
        obtain ⟨k, hk⟩ := step_of_fc_pos _ this
        have h1 : cwShift i₀ (right j₀) < sys.rs.n - 1 := by
          rw [cwShift_right_step hN4 i₀ j₀ hd_j₀_lt]; omega
        exact ⟨_, k, hk, by
          rw [cwShift_right_step hN4 i₀ (right j₀) h1,
            cwShift_right_step hN4 i₀ j₀ hd_j₀_lt]; omega⟩
    -- Walk visits d = 1 (at k_rr) and d > d(j₀) > 1 (at k_q). IVT gives d(j₀).
    obtain ⟨k_hit, hk_hit⟩ := walk_visits_between' gc i₀ hfc0 k_rr k_q
      (cwShift i₀ j₀)
      (by simp [hd_rr_eq]; omega)
      (by simp [hk_q]; omega)
    exact absurd (cwShift_injective hN4 i₀ hk_hit) (moverAt_ne_of_fc_zero gc j₀ hfc_j₀ k_hit)

/-- **Firing support reduction (|Z| ≥ 3 case).**
    If ≥ 3 processors never fire, the zero set is a contiguous arc (from
    firingSupport_connected_arc), giving 3 consecutive non-firing procs.
    By no_three_consecutive_zeroFC, this contradicts hno_safe. -/
theorem zeroSet_ge3_impossible (gc : GoodCycle sys)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hn : sys.rs.n ≥ 9)
    (hZ_ge3 : (zeroSet gc).card ≥ 3) :
    False := by
  obtain ⟨i, hfc_i, hfc_ri, hfc_rri⟩ := firingSupport_connected_arc gc hno_safe hn hZ_ge3
  have hfc_rri_pos := no_three_consecutive_zeroFC gc hno_safe i hfc_i hfc_ri
  omega

/-- **If any processor has fireCount = 0, the good cycle has zero winding.**

    Proof: fc(q) = 0 → cwMoveCountAt q = 0 and ccwMoveCountAt q = 0.
    edgeNetFlow q = cwMoveCountAt q - ccwMoveCountAt (right q) ≤ 0  (since cw = 0).
    edgeNetFlow (left q) = cwMoveCountAt (left q) - ccwMoveCountAt q ≥ 0  (since ccw = 0).
    By edgeNetFlow_constant, they're equal ⇒ both = 0.
    totalDisplacement = n · 0 = 0. -/
theorem zeroWinding_of_fc_zero (gc : GoodCycle sys)
    (q : Fin sys.rs.n) (hfc : gc.fireCount q = 0) :
    gc.zeroWinding := by
  -- Step 1: q never fires
  have hq_never : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ q :=
    fun k => moverAt_ne_of_fc_zero gc q hfc k
  -- Step 2: cwMoveCountAt q = 0 and ccwMoveCountAt q = 0
  have hcw0 : gc.cwMoveCountAt q = 0 := by
    unfold GoodCycle.cwMoveCountAt
    apply Finset.sum_eq_zero; intro k _; simp [hq_never k]
  have hccw0 : gc.ccwMoveCountAt q = 0 := by
    unfold GoodCycle.ccwMoveCountAt
    apply Finset.sum_eq_zero; intro k _; simp [hq_never k]
  -- Step 3: edgeNetFlow q ≤ 0 (cw part = 0)
  have hflow_q : gc.edgeNetFlow q = (0 : Int) - gc.ccwMoveCountAt (right q) := by
    unfold GoodCycle.edgeNetFlow; rw [hcw0]; simp
  have hflow_q_le : gc.edgeNetFlow q ≤ 0 := by rw [hflow_q]; omega
  -- Step 4: edgeNetFlow (left q) ≥ 0 (ccw part = 0)
  have hflow_lq : gc.edgeNetFlow (left q) = (gc.cwMoveCountAt (left q) : Int) - 0 := by
    unfold GoodCycle.edgeNetFlow
    have hrlq : right (left q) = q := right_left_eq_self q
    rw [hrlq, hccw0]; simp
  have hflow_lq_ge : gc.edgeNetFlow (left q) ≥ 0 := by rw [hflow_lq]; omega
  -- Step 5: they're equal → both = 0
  have hflow_eq : gc.edgeNetFlow q = gc.edgeNetFlow (left q) :=
    gc.edgeNetFlow_constant (left q) q
  have hflow_zero : gc.edgeNetFlow q = 0 := by omega
  -- Step 6: totalDisplacement = n · 0 = 0
  unfold GoodCycle.zeroWinding
  rw [gc.totalDisplacement_eq_n_mul_edgeNetFlow q, hflow_zero]
  simp


/-! ### Phase decomposition infrastructure -/

/-- fireCount equals intervalFireCount over the full cycle [0, configs.length). -/
theorem fireCount_eq_intervalFireCount_full (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    gc.fireCount p = gc.intervalFireCount p 0 gc.configs.length := by
  unfold GoodCycle.fireCount GoodCycle.intervalFireCount GoodCycle.prefixFireCount
  simp

/-- If processor t fires at steps a and b (consecutive, no t-fire between), and then
    at steps b and c (consecutive, no t-fire between), the fire counts add up:
    intervalFireCount p a c = intervalFireCount p a b + intervalFireCount p b c. -/
theorem intervalFireCount_add_phases (gc : GoodCycle sys) (p : Fin sys.rs.n)
    {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) :
    gc.intervalFireCount p a c =
      gc.intervalFireCount p a b + gc.intervalFireCount p b c :=
  intervalFireCount_split gc p hab hbc

/-- Helper: if every consecutive t-pair has iFC(q) ≥ 1, then for any two
    t-fire positions a < b, iFC(q, a, b) ≥ iFC(t, a, b).
    Proof by strong induction on b - a. -/
private theorem ifc_q_ge_ifc_t_of_all_consec_pos
    (gc : GoodCycle sys) (t q : Fin sys.rs.n)
    (hall : ∀ (a s : Fin gc.configs.length),
      a.val < s.val → gc.moverAt a = t → gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      gc.intervalFireCount q a.val s.val ≥ 1)
    : ∀ (d : Nat) (a b : Fin gc.configs.length),
      b.val - a.val ≤ d → a.val < b.val →
      gc.moverAt a = t → gc.moverAt b = t →
      gc.intervalFireCount q a.val b.val ≥ gc.intervalFireCount t a.val b.val := by
  intro d
  induction d with
  | zero => intro a b hd hab; omega
  | succ d ih =>
    intro a b hd hab ha hb
    by_cases hconsec : ∀ k : Fin gc.configs.length,
        a.val < k.val → k.val < b.val → gc.moverAt k ≠ t
    · -- Consecutive: iFC(t, a, b) = 1, iFC(q, a, b) ≥ 1
      have hge1 := hall a b hab ha hb hconsec
      have htone : gc.intervalFireCount t a.val b.val = 1 := by
        have h1 : gc.intervalFireCount t a.val (a.val + 1) = 1 := by
          rw [intervalFireCount_single gc t a.isLt]; simp [ha]
        have h0 : gc.intervalFireCount t (a.val + 1) b.val = 0 := by
          apply intervalFireCount_eq_zero_of_noFire gc t (by omega) (by omega)
          intro k hk1 hk2; exact hconsec k (by omega) hk2
        have := intervalFireCount_split gc t (show a.val ≤ a.val + 1 by omega)
          (show a.val + 1 ≤ b.val by omega)
        omega
      omega
    · -- Not consecutive: find intermediate t-fire c
      push_neg at hconsec
      obtain ⟨c, hac, hcb, hc⟩ := hconsec
      -- Apply IH to (a, c) and (c, b)
      have ih_ac := ih a c (by omega) hac ha hc
      have ih_cb := ih c b (by omega) hcb hc hb
      -- Additivity
      have split_q := intervalFireCount_split gc q (show a.val ≤ c.val by omega)
        (show c.val ≤ b.val by omega)
      have split_t := intervalFireCount_split gc t (show a.val ≤ c.val by omega)
        (show c.val ≤ b.val by omega)
      omega

/-- Key pigeonhole lemma: if processor q fires sufficiently fewer times than t,
    there exist consecutive t-firing steps with zero q-fires in between.

    The hypothesis requires fc(q) + 2 ≤ fc(t), which gives room for the
    pigeonhole argument on the P-1 interior intervals between the first and
    last t-fire positions. -/
theorem exists_consecutive_tfire_with_zero_qfire
    (gc : GoodCycle sys) (t q : Fin sys.rs.n)
    (hfc_t_ge2 : gc.fireCount t ≥ 2)
    (hfc_t_lt_L : gc.fireCount t < gc.configs.length)
    (hfc_q_lt_t : gc.fireCount q + 2 ≤ gc.fireCount t) :
    ∃ (a s : Fin gc.configs.length),
      a.val < s.val ∧
      gc.moverAt a = t ∧ gc.moverAt s = t ∧
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) ∧
      gc.intervalFireCount q a.val s.val = 0 := by
  -- By contradiction: assume every consecutive t-pair has iFC(q) ≥ 1
  by_contra hall_neg
  push_neg at hall_neg
  -- hall_neg : ∀ a s, ... → iFC q a s ≠ 0, i.e., iFC q a s ≥ 1
  have hall : ∀ (a s : Fin gc.configs.length),
      a.val < s.val → gc.moverAt a = t → gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      gc.intervalFireCount q a.val s.val ≥ 1 := by
    intro a s h1 h2 h3 h4
    exact Nat.one_le_iff_ne_zero.mpr (hall_neg a s h1 h2 h3 h4)
  -- Step 1: find first and last t-fire positions
  have hL_pos := gc.configs_length_pos
  let tFires : Finset (Fin gc.configs.length) :=
    Finset.univ.filter (fun k => gc.moverAt k = t)
  have htFires_ne : tFires.Nonempty := by
    have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc_t_ge2
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  let s_min : Fin gc.configs.length := tFires.min' htFires_ne
  let s_max : Fin gc.configs.length := tFires.max' htFires_ne
  have hs_min_mem : s_min ∈ tFires := Finset.min'_mem tFires htFires_ne
  have hs_max_mem : s_max ∈ tFires := Finset.max'_mem tFires htFires_ne
  have hs_min_fire : gc.moverAt s_min = t :=
    (Finset.mem_filter.mp hs_min_mem).2
  have hs_max_fire : gc.moverAt s_max = t :=
    (Finset.mem_filter.mp hs_max_mem).2
  -- s_min < s_max (there are ≥ 2 t-fires, so min ≠ max)
  have hs_ne : s_min ≠ s_max := by
    intro heq
    -- If min = max, all t-fires are at the same position
    have huniq : ∀ k ∈ tFires, k = s_min := by
      intro k hk
      have hle1 : s_min ≤ k := Finset.min'_le tFires k hk
      have hle2 : k ≤ s_max := Finset.le_max' tFires k hk
      rw [← heq] at hle2; exact le_antisymm hle2 hle1
    -- So fireCount t = 1
    have hfc_le1 : gc.fireCount t ≤ 1 := by
      rw [gc.fireCount_eq_sum_moverAt t]
      have hbd : ∀ j : Fin gc.configs.length,
          (if gc.moverAt j = t then (1 : Nat) else 0) ≤
            (if j = s_min then 1 else 0) := by
        intro j
        by_cases hj : gc.moverAt j = t
        · have : j ∈ tFires := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
          rw [huniq j this]; simp [hs_min_fire]
        · simp [hj]
      calc ∑ j, (if gc.moverAt j = t then (1 : Nat) else 0)
          ≤ ∑ j, (if j = s_min then 1 else 0) :=
            Finset.sum_le_sum (fun j _ => hbd j)
        _ = 1 := by
            rw [Finset.sum_eq_single s_min
              (fun b _ hb => by simp [hb]) (by simp)]; simp
    omega
  have hs_lt : s_min.val < s_max.val := by
    have hle : s_min ≤ s_max := Finset.min'_le tFires s_max hs_max_mem
    exact lt_of_le_of_ne hle (fun h => hs_ne (Fin.ext h))
  -- Step 2: iFC(t, 0, s_min) = 0 (no t-fires before the minimum)
  have hifc_t_before : gc.intervalFireCount t 0 s_min.val = 0 := by
    apply intervalFireCount_eq_zero_of_noFire gc t (Nat.zero_le _) (Nat.le_of_lt s_min.isLt)
    intro k hk1 hk2
    intro hfire
    have hk_mem : k ∈ tFires := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hfire⟩
    have := Finset.min'_le tFires k hk_mem
    omega
  -- Step 3: iFC(t, s_max, L) = 1 (only s_max in [s_max, L))
  have hifc_t_after : gc.intervalFireCount t s_max.val gc.configs.length = 1 := by
    have h_smax_one : gc.intervalFireCount t s_max.val (s_max.val + 1) = 1 := by
      rw [intervalFireCount_single gc t s_max.isLt]; simp [hs_max_fire]
    have h_after_zero : gc.intervalFireCount t (s_max.val + 1) gc.configs.length = 0 := by
      apply intervalFireCount_eq_zero_of_noFire gc t (by omega) le_rfl
      intro k hk1 hk2
      intro hfire
      have hk_mem : k ∈ tFires := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hfire⟩
      have := Finset.le_max' tFires k hk_mem
      omega
    have := intervalFireCount_split gc t (show s_max.val ≤ s_max.val + 1 by omega)
      (show s_max.val + 1 ≤ gc.configs.length by omega)
    omega
  -- Step 4: iFC(t, s_min, s_max) = fireCount t - 1
  have hifc_t_mid : gc.intervalFireCount t s_min.val s_max.val = gc.fireCount t - 1 := by
    have hfull := fireCount_eq_intervalFireCount_full gc t
    have split_mid := intervalFireCount_split gc t (show s_min.val ≤ s_max.val by omega)
      (show s_max.val ≤ gc.configs.length by exact Nat.le_of_lt s_max.isLt)
    have split_all := intervalFireCount_split gc t (Nat.zero_le s_min.val)
      (show s_min.val ≤ gc.configs.length by exact Nat.le_of_lt s_min.isLt)
    -- fireCount t = iFC(0, L) = iFC(0, s_min) + iFC(s_min, L)
    --            = 0 + (iFC(s_min, s_max) + 1)
    rw [← hfull, split_mid] at split_all
    omega
  -- Step 5: iFC(q, s_min, s_max) ≥ iFC(t, s_min, s_max) from helper
  have hge := ifc_q_ge_ifc_t_of_all_consec_pos gc t q hall
    (s_max.val - s_min.val) s_min s_max le_rfl hs_lt hs_min_fire hs_max_fire
  -- Step 6: iFC(q, s_min, s_max) ≤ fireCount q
  have hle : gc.intervalFireCount q s_min.val s_max.val ≤ gc.fireCount q := by
    have hfull := fireCount_eq_intervalFireCount_full gc q
    have split_mid := intervalFireCount_split gc q (show s_min.val ≤ s_max.val by omega)
      (show s_max.val ≤ gc.configs.length by exact Nat.le_of_lt s_max.isLt)
    have split_all := intervalFireCount_split gc q (Nat.zero_le s_min.val)
      (show s_min.val ≤ gc.configs.length by exact Nat.le_of_lt s_min.isLt)
    -- fireCount q = iFC(0, s_min) + iFC(s_min, s_max) + iFC(s_max, L)
    rw [← hfull, split_mid] at split_all
    omega
  -- Step 7: contradiction
  -- fireCount t - 1 ≤ iFC(q, s_min, s_max) ≤ fireCount q ≤ fireCount t - 2
  omega

/-! ### Cyclic config preservation -/

/-- Config value preservation across the cycle boundary: if processor q doesn't
    fire in [b, L) ∪ [0, a) (where a ≤ b cyclically, i.e., b > a after wrap),
    then configs.get(b)(q) = configs.get(a)(q).

    Chains three facts:
    1. configVal_eq_of_noFire_between for [b, L-1]
    2. gc.state_eq_of_ne_moverAt at step L-1 (wrap to step 0)
    3. configVal_eq_of_noFire_between for [0, a) -/
private theorem configVal_eq_of_cyclic_noFire
    (gc : GoodCycle sys) (q : Fin sys.rs.n) (a b : Nat)
    (ha : a < gc.configs.length) (hb : b < gc.configs.length)
    (_hab : a ≤ b)
    (hnofire_tail : ∀ k : Fin gc.configs.length,
      b ≤ k.val → gc.moverAt k ≠ q)
    (hnofire_head : ∀ k : Fin gc.configs.length,
      k.val < a → gc.moverAt k ≠ q) :
    (gc.configs.get ⟨b, hb⟩) q = (gc.configs.get ⟨a, ha⟩) q := by
  have hL_pos := gc.configs_length_pos
  have hL1_lt : gc.configs.length - 1 < gc.configs.length := by omega
  have hb_le_L1 : b ≤ gc.configs.length - 1 := by omega
  -- Step 1: config(b)(q) = config(L-1)(q)
  have h_tail : (gc.configs.get ⟨b, hb⟩) q =
      (gc.configs.get ⟨gc.configs.length - 1, hL1_lt⟩) q := by
    by_cases hb_last : b = gc.configs.length - 1
    · rw [show (⟨b, hb⟩ : Fin gc.configs.length) = ⟨gc.configs.length - 1, hL1_lt⟩ from
        Fin.ext hb_last]
    · exact configVal_eq_of_noFire_between gc q b (gc.configs.length - 1)
        hb_le_L1 hL1_lt (fun k hk1 hk2 => hnofire_tail k (by omega))
  -- Step 2: config(L-1)(q) = config(0)(q) via cycle wrap
  have hq_ne_last : q ≠ gc.moverAt ⟨gc.configs.length - 1, hL1_lt⟩ :=
    fun heq => hnofire_tail ⟨gc.configs.length - 1, hL1_lt⟩ hb_le_L1 heq.symm
  have h_wrap_idx : nextIndex gc.configs ⟨gc.configs.length - 1, hL1_lt⟩ =
      ⟨0, hL_pos⟩ :=
    Fin.ext (by simp [nextIndex, show gc.configs.length - 1 + 1 = gc.configs.length by omega,
      Nat.mod_self])
  have h_wrap : (gc.configs.get ⟨gc.configs.length - 1, hL1_lt⟩) q =
      (gc.configs.get ⟨0, hL_pos⟩) q := by
    have := gc.state_eq_of_ne_moverAt ⟨gc.configs.length - 1, hL1_lt⟩ q hq_ne_last
    rw [h_wrap_idx] at this; exact this.symm
  -- Step 3: config(0)(q) = config(a)(q)
  have h_head : (gc.configs.get ⟨0, hL_pos⟩) q =
      (gc.configs.get ⟨a, ha⟩) q := by
    by_cases ha0 : a = 0
    · rw [show (⟨0, hL_pos⟩ : Fin gc.configs.length) = ⟨a, ha⟩ from Fin.ext ha0.symm]
    · exact configVal_eq_of_noFire_between gc q 0 a (Nat.zero_le _) ha
        (fun k hk1 hk2 => hnofire_head k hk2)
  exact h_tail.trans (h_wrap.trans h_head)

/-- Combined fire count over two intervals (wrap-around): the sum of fires
    in [s_max+1, L) and [0, s_min) equals the difference of the full fire
    count and the interior fire count. -/
theorem wrap_ifc_eq
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    {s_min s_max : Nat}
    (hs_min_lt : s_min < gc.configs.length)
    (hs_max_lt : s_max < gc.configs.length)
    (hs_lt : s_min ≤ s_max) :
    gc.intervalFireCount p 0 s_min +
      gc.intervalFireCount p (s_max + 1) gc.configs.length =
    gc.fireCount p - gc.intervalFireCount p s_min (s_max + 1) := by
  have hfull := fireCount_eq_intervalFireCount_full gc p
  have h1 := intervalFireCount_split gc p (Nat.zero_le s_min)
    (show s_min ≤ gc.configs.length from Nat.le_of_lt hs_min_lt)
  have h2 := intervalFireCount_split gc p
    (show s_min ≤ s_max + 1 by omega)
    (show s_max + 1 ≤ gc.configs.length by omega)
  -- fc(p) = ifc(0, s_min) + ifc(s_min, s_max+1) + ifc(s_max+1, L)
  -- Goal: ifc(0, s_min) + ifc(s_max+1, L) = fc(p) - ifc(s_min, s_max+1)
  have hmono : gc.intervalFireCount p s_min (s_max + 1) ≤ gc.fireCount p := by
    rw [hfull, h1, h2]; omega
  omega

/-! ### Phase sum bounds via interior decomposition -/

/-- Upper bound on combined fire counts by strong induction on consecutive
    t-fire pairs. If every consecutive t-pair (a,s) has
    ifc(p₁,a,s) + ifc(p₂,a,s) ≤ 1, then for any two t-fire positions a < b,
    ifc(p₁,a,b) + ifc(p₂,a,b) ≤ ifc(t,a,b).

    Proof: each consecutive pair contributes sum ≤ 1 and exactly 1 t-fire.
    Multiple pairs combine via additivity. -/
theorem ifc_sum_le_of_consec_le1
    (gc : GoodCycle sys) (t p₁ p₂ : Fin sys.rs.n)
    (hall : ∀ (a s : Fin gc.configs.length),
      a.val < s.val → gc.moverAt a = t → gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      gc.intervalFireCount p₁ a.val s.val + gc.intervalFireCount p₂ a.val s.val ≤ 1)
    : ∀ (d : Nat) (a b : Fin gc.configs.length),
      b.val - a.val ≤ d → a.val < b.val →
      gc.moverAt a = t → gc.moverAt b = t →
      gc.intervalFireCount p₁ a.val b.val + gc.intervalFireCount p₂ a.val b.val ≤
        gc.intervalFireCount t a.val b.val := by
  intro d
  induction d with
  | zero => intro a b hd hab; omega
  | succ d ih =>
    intro a b hd hab ha hb
    by_cases hconsec : ∀ k : Fin gc.configs.length,
        a.val < k.val → k.val < b.val → gc.moverAt k ≠ t
    · -- Consecutive: ifc(t, a, b) = 1, sum ≤ 1.
      have hle1 := hall a b hab ha hb hconsec
      have h_t_one : gc.intervalFireCount t a.val (a.val + 1) = 1 := by
        rw [intervalFireCount_single gc t a.isLt]; simp [ha]
      have h_t_rest : gc.intervalFireCount t (a.val + 1) b.val = 0 := by
        apply intervalFireCount_eq_zero_of_noFire gc t (by omega) (by omega)
        intro k hk1 hk2; exact hconsec k (by omega) hk2
      have h_t_split := intervalFireCount_split gc t
        (show a.val ≤ a.val + 1 by omega) (show a.val + 1 ≤ b.val by omega)
      omega
    · -- Not consecutive: find intermediate t-fire c
      push_neg at hconsec
      obtain ⟨c, hac, hcb, hc⟩ := hconsec
      have ih_ac := ih a c (by omega) hac ha hc
      have ih_cb := ih c b (by omega) hcb hc hb
      have split_p₁ := intervalFireCount_split gc p₁ (show a.val ≤ c.val by omega)
        (show c.val ≤ b.val by omega)
      have split_p₂ := intervalFireCount_split gc p₂ (show a.val ≤ c.val by omega)
        (show c.val ≤ b.val by omega)
      have split_t := intervalFireCount_split gc t (show a.val ≤ c.val by omega)
        (show c.val ≤ b.val by omega)
      omega

/-- Lower bound on combined fire counts: if every consecutive t-pair has
    ifc(p₁) + ifc(p₂) ≥ 1, then for any two t-fire positions a < b,
    ifc(p₁,a,b) + ifc(p₂,a,b) ≥ ifc(t,a,b).

    This is the combined version of ifc_q_ge_ifc_t_of_all_consec_pos:
    base case gives sum ≥ 1 = ifc(t) for consecutive pair, inductive
    step uses additivity. -/
theorem ifc_sum_ge_of_consec_ge1
    (gc : GoodCycle sys) (t p₁ p₂ : Fin sys.rs.n)
    (hall : ∀ (a s : Fin gc.configs.length),
      a.val < s.val → gc.moverAt a = t → gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      gc.intervalFireCount p₁ a.val s.val + gc.intervalFireCount p₂ a.val s.val ≥ 1)
    : ∀ (d : Nat) (a b : Fin gc.configs.length),
      b.val - a.val ≤ d → a.val < b.val →
      gc.moverAt a = t → gc.moverAt b = t →
      gc.intervalFireCount p₁ a.val b.val + gc.intervalFireCount p₂ a.val b.val ≥
        gc.intervalFireCount t a.val b.val := by
  intro d
  induction d with
  | zero => intro a b hd hab; omega
  | succ d ih =>
    intro a b hd hab ha hb
    by_cases hconsec : ∀ k : Fin gc.configs.length,
        a.val < k.val → k.val < b.val → gc.moverAt k ≠ t
    · -- Consecutive: ifc(t, a, b) = 1, sum ≥ 1.
      have hge1 := hall a b hab ha hb hconsec
      have htone : gc.intervalFireCount t a.val b.val = 1 := by
        have h1 : gc.intervalFireCount t a.val (a.val + 1) = 1 := by
          rw [intervalFireCount_single gc t a.isLt]; simp [ha]
        have h0 : gc.intervalFireCount t (a.val + 1) b.val = 0 := by
          apply intervalFireCount_eq_zero_of_noFire gc t (by omega) (by omega)
          intro k hk1 hk2; exact hconsec k (by omega) hk2
        have := intervalFireCount_split gc t (show a.val ≤ a.val + 1 by omega)
          (show a.val + 1 ≤ b.val by omega)
        omega
      omega
    · -- Not consecutive: find intermediate t-fire c
      push_neg at hconsec
      obtain ⟨c, hac, hcb, hc⟩ := hconsec
      have ih_ac := ih a c (by omega) hac ha hc
      have ih_cb := ih c b (by omega) hcb hc hb
      have split_p₁ := intervalFireCount_split gc p₁ (show a.val ≤ c.val by omega)
        (show c.val ≤ b.val by omega)
      have split_p₂ := intervalFireCount_split gc p₂ (show a.val ≤ c.val by omega)
        (show c.val ≤ b.val by omega)
      have split_t := intervalFireCount_split gc t (show a.val ≤ c.val by omega)
        (show c.val ≤ b.val by omega)
      omega

/-! ### Sparse phase sum bounds -/

/-- Variant: if the sum of fire counts of two processors is strictly less than
    fireCount(t), and each phase has their combined interval fire count ≥ 1,
    then each phase has combined count exactly 1.

    Proof: by contradiction. If some consecutive t-pair has combined ifc ≥ 2,
    split [s_min, s_max] at that pair. The sub-intervals contribute ≥ ifc(t)
    by ifc_sum_ge_of_consec_ge1, plus the extra ≥ 2 gives total ≥ fc(t).
    But total ≤ fc(p₁)+fc(p₂) < fc(t). Contradiction. -/
theorem phase_tight_of_sum_le
    (gc : GoodCycle sys) (t p₁ p₂ : Fin sys.rs.n)
    (hfc_t_ge2 : gc.fireCount t ≥ 2)
    (hfc_t_lt_L : gc.fireCount t < gc.configs.length)
    (hsum_le : gc.fireCount p₁ + gc.fireCount p₂ + 1 ≤ gc.fireCount t)
    (hall_ge1 : ∀ (a s : Fin gc.configs.length),
      a.val < s.val →
      gc.moverAt a = t → gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      gc.intervalFireCount p₁ a.val s.val + gc.intervalFireCount p₂ a.val s.val ≥ 1) :
    ∀ (a s : Fin gc.configs.length),
      a.val < s.val →
      gc.moverAt a = t → gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      gc.intervalFireCount p₁ a.val s.val + gc.intervalFireCount p₂ a.val s.val = 1 := by
  intro a s has ha hs hconsec
  apply Nat.le_antisymm
  · -- ≤ 1: by contradiction, assume ≥ 2
    by_contra hge2; push_neg at hge2
    -- Find first and last t-fire positions
    have hL_pos := gc.configs_length_pos
    let tFires : Finset (Fin gc.configs.length) :=
      Finset.univ.filter (fun k => gc.moverAt k = t)
    have htFires_ne : tFires.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
    let s_min : Fin gc.configs.length := tFires.min' htFires_ne
    let s_max : Fin gc.configs.length := tFires.max' htFires_ne
    have hs_min_fire : gc.moverAt s_min = t :=
      (Finset.mem_filter.mp (Finset.min'_mem tFires htFires_ne)).2
    have hs_max_fire : gc.moverAt s_max = t :=
      (Finset.mem_filter.mp (Finset.max'_mem tFires htFires_ne)).2
    -- a and s are t-fires, so s_min ≤ a < s ≤ s_max
    have ha_mem : a ∈ tFires := Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩
    have hs_mem : s ∈ tFires := Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩
    have hsmin_le_a : s_min.val ≤ a.val := Finset.min'_le tFires a ha_mem
    have hs_le_smax : s.val ≤ s_max.val := Finset.le_max' tFires s hs_mem
    -- ifc(t, 0, s_min) = 0 (no t-fires before first)
    have hifc_t_before : gc.intervalFireCount t 0 s_min.val = 0 := by
      apply intervalFireCount_eq_zero_of_noFire gc t (Nat.zero_le _)
        (Nat.le_of_lt s_min.isLt)
      intro k hk1 hk2 hfire
      have hk_mem : k ∈ tFires := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hfire⟩
      have := Finset.min'_le tFires k hk_mem; omega
    -- ifc(t, s_max, L) = 1
    have hifc_t_after : gc.intervalFireCount t s_max.val gc.configs.length = 1 := by
      have h1 : gc.intervalFireCount t s_max.val (s_max.val + 1) = 1 := by
        rw [intervalFireCount_single gc t s_max.isLt]; simp [hs_max_fire]
      have h0 : gc.intervalFireCount t (s_max.val + 1) gc.configs.length = 0 := by
        apply intervalFireCount_eq_zero_of_noFire gc t (by omega) le_rfl
        intro k hk1 hk2 hfire
        have hk_mem : k ∈ tFires := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hfire⟩
        have := Finset.le_max' tFires k hk_mem; omega
      have := intervalFireCount_split gc t (show s_max.val ≤ s_max.val + 1 by omega)
        (show s_max.val + 1 ≤ gc.configs.length by omega)
      omega
    -- ifc(t, s_min, s_max) = fc(t) - 1
    have hifc_t_mid : gc.intervalFireCount t s_min.val s_max.val = gc.fireCount t - 1 := by
      have hfull := fireCount_eq_intervalFireCount_full gc t
      have split_mid := intervalFireCount_split gc t (show s_min.val ≤ s_max.val by omega)
        (show s_max.val ≤ gc.configs.length from Nat.le_of_lt s_max.isLt)
      have split_all := intervalFireCount_split gc t (Nat.zero_le s_min.val)
        (show s_min.val ≤ gc.configs.length from Nat.le_of_lt s_min.isLt)
      rw [← hfull, split_mid] at split_all; omega
    -- ifc(t, a, s) = 1 (consecutive pair)
    have hifc_t_as : gc.intervalFireCount t a.val s.val = 1 := by
      have h1 : gc.intervalFireCount t a.val (a.val + 1) = 1 := by
        rw [intervalFireCount_single gc t a.isLt]; simp [ha]
      have h0 : gc.intervalFireCount t (a.val + 1) s.val = 0 := by
        apply intervalFireCount_eq_zero_of_noFire gc t (by omega) (by omega)
        intro k hk1 hk2; exact hconsec k (by omega) hk2
      have := intervalFireCount_split gc t (show a.val ≤ a.val + 1 by omega)
        (show a.val + 1 ≤ s.val by omega)
      omega
    -- Split sum(s_min, s_max) at a and s
    have split_p₁_1 := intervalFireCount_split gc p₁ hsmin_le_a
      (show a.val ≤ s_max.val by omega)
    have split_p₁_2 := intervalFireCount_split gc p₁ (show a.val ≤ s.val by omega)
      hs_le_smax
    have split_p₂_1 := intervalFireCount_split gc p₂ hsmin_le_a
      (show a.val ≤ s_max.val by omega)
    have split_p₂_2 := intervalFireCount_split gc p₂ (show a.val ≤ s.val by omega)
      hs_le_smax
    -- sum(s_min, a) ≥ ifc(t, s_min, a) via ifc_sum_ge_of_consec_ge1 (if s_min < a)
    have hge_left : gc.intervalFireCount p₁ s_min.val a.val +
        gc.intervalFireCount p₂ s_min.val a.val ≥
        gc.intervalFireCount t s_min.val a.val := by
      by_cases heq : s_min.val = a.val
      · simp [show s_min.val = a.val from heq,
          show gc.intervalFireCount p₁ a.val a.val = 0 from by
            unfold GoodCycle.intervalFireCount; omega,
          show gc.intervalFireCount p₂ a.val a.val = 0 from by
            unfold GoodCycle.intervalFireCount; omega,
          show gc.intervalFireCount t a.val a.val = 0 from by
            unfold GoodCycle.intervalFireCount; omega]
      · exact ifc_sum_ge_of_consec_ge1 gc t p₁ p₂ hall_ge1
          (a.val - s_min.val) s_min a le_rfl
          (by omega) hs_min_fire ha
    -- sum(s, s_max) ≥ ifc(t, s, s_max) (if s < s_max)
    have hge_right : gc.intervalFireCount p₁ s.val s_max.val +
        gc.intervalFireCount p₂ s.val s_max.val ≥
        gc.intervalFireCount t s.val s_max.val := by
      by_cases heq : s.val = s_max.val
      · simp [show s.val = s_max.val from heq,
          show gc.intervalFireCount p₁ s_max.val s_max.val = 0 from by
            unfold GoodCycle.intervalFireCount; omega,
          show gc.intervalFireCount p₂ s_max.val s_max.val = 0 from by
            unfold GoodCycle.intervalFireCount; omega,
          show gc.intervalFireCount t s_max.val s_max.val = 0 from by
            unfold GoodCycle.intervalFireCount; omega]
      · exact ifc_sum_ge_of_consec_ge1 gc t p₁ p₂ hall_ge1
          (s_max.val - s.val) s s_max le_rfl
          (by omega) hs hs_max_fire
    -- ifc(t, s_min, s_max) = ifc(t, s_min, a) + 1 + ifc(t, s, s_max)
    have split_t_1 := intervalFireCount_split gc t hsmin_le_a
      (show a.val ≤ s_max.val by omega)
    have split_t_2 := intervalFireCount_split gc t (show a.val ≤ s.val by omega)
      hs_le_smax
    -- sum(s_min, s_max) ≥ ifc(t, s_min, a) + 2 + ifc(t, s, s_max)
    --                    = ifc(t, s_min, s_max) + 1 = fc(t)
    -- But sum(s_min, s_max) ≤ fc(p₁) + fc(p₂) ≤ fc(t) - 1. Contradiction.
    have hfc_p₁_ge : gc.intervalFireCount p₁ s_min.val s_max.val ≤
        gc.fireCount p₁ := by
      have hfull := fireCount_eq_intervalFireCount_full gc p₁
      have h1 := intervalFireCount_split gc p₁ (Nat.zero_le s_min.val)
        (show s_min.val ≤ gc.configs.length from Nat.le_of_lt s_min.isLt)
      have h2 := intervalFireCount_split gc p₁ (show s_min.val ≤ s_max.val by omega)
        (show s_max.val ≤ gc.configs.length from Nat.le_of_lt s_max.isLt)
      omega
    have hfc_p₂_ge : gc.intervalFireCount p₂ s_min.val s_max.val ≤
        gc.fireCount p₂ := by
      have hfull := fireCount_eq_intervalFireCount_full gc p₂
      have h1 := intervalFireCount_split gc p₂ (Nat.zero_le s_min.val)
        (show s_min.val ≤ gc.configs.length from Nat.le_of_lt s_min.isLt)
      have h2 := intervalFireCount_split gc p₂ (show s_min.val ≤ s_max.val by omega)
        (show s_max.val ≤ gc.configs.length from Nat.le_of_lt s_max.isLt)
      omega
    omega
  · -- ≥ 1: direct from hall_ge1
    exact hall_ge1 a s has ha hs hconsec

/-- Helper: left t ≠ t for n ≥ 4. -/
private theorem left_ne_self_peb (t : Fin sys.rs.n) : left t ≠ t := by
  intro h
  have hn := sys.rs.n_ge_4
  have ht := t.isLt
  have hval := congrArg Fin.val h
  simp only [left_val] at hval
  by_cases h0 : t.val = 0
  · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hval; omega
  · rw [show t.val + sys.rs.n - 1 = (t.val - 1) + sys.rs.n from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hval; omega

/-- Helper: right t ≠ t for n ≥ 4. -/
private theorem right_ne_self_peb (t : Fin sys.rs.n) : right t ≠ t := by
  intro h
  have hn := sys.rs.n_ge_4
  have ht := t.isLt
  have hval := congrArg Fin.val h
  simp only [right_val] at hval
  -- hval : (t.val + 1) % sys.rs.n = t.val
  have hmod := Nat.mod_lt (t.val + 1) (by omega : 0 < sys.rs.n)
  by_cases hlast : t.val + 1 = sys.rs.n
  · rw [hlast, Nat.mod_self] at hval; omega
  · rw [Nat.mod_eq_of_lt (by omega)] at hval; omega

/-- Sparse phase sum bound (≥ direction): if all phases of t have normal form
    and there is no entry conflict, then fc(L) + fc(R) ≥ fc(t).

    Proof strategy:
    1. Show every consecutive t-pair has ifc(L)+ifc(R) ≥ 1 (from normalForm).
    2. Apply ifc_sum_ge_of_consec_ge1 on [s_min, s_max] to get sum ≥ ifc(t) = fc(t)-1.
    3. Parity: fc(L)+fc(R) is even, so if fc(t)-1 is odd, we upgrade to ≥ fc(t).
    4. For fc(t) odd: the wrap-around phase contributes the extra fire. -/
theorem sparse_phase_sum_ge
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (hfc_t_ge2 : gc.fireCount t ≥ 2)
    (hfc_t_lt_L : gc.fireCount t < gc.configs.length)
    (hall_normal : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hnoEC : ¬hasEntryConflict gc)
    (hno_consec : ∀ (a s : Fin gc.configs.length),
      a.val < s.val → gc.moverAt a = t → gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      a.val + 1 < s.val)
    (hno_cyclic_consec : ∀ k : Fin gc.configs.length, gc.moverAt k = t →
      gc.moverAt ⟨(k.val + 1) % gc.configs.length,
        Nat.mod_lt _ gc.configs_length_pos⟩ ≠ t) :
    gc.fireCount (left t) + gc.fireCount (right t) ≥ gc.fireCount t := by
  -- Step 1: Every consecutive t-pair has J+K ≥ 1
  have hall_ge1 : ∀ (a s : Fin gc.configs.length),
      a.val < s.val → gc.moverAt a = t → gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      gc.intervalFireCount (left t) a.val s.val +
        gc.intervalFireCount (right t) a.val s.val ≥ 1 := by
    intro a s has ha hs hno
    by_cases hgap : a.val + 1 < s.val
    · -- Non-empty gap: construct TernaryPhase at (a+1, s)
      have ha1_lt : a.val + 1 < gc.configs.length := by omega
      -- Non-empty gap: TernaryPhase at (a+1, s) has normalForm → J+K ≥ 1.
      -- ifc on [a, a+1) = 0 (t fires at a, not L or R) so interval [a, s) has
      -- the same J+K as the phase [a+1, s). normalForm → not BothEven(0,0) → J+K ≥ 1.
      -- Construct the TernaryPhase at (a+1, s)
      let a1 : Fin gc.configs.length := ⟨a.val + 1, ha1_lt⟩
      have ha1_nonmover : gc.moverAt a1 ≠ t :=
        hno ⟨a.val + 1, ha1_lt⟩
          (show a.val < (⟨a.val + 1, ha1_lt⟩ : Fin gc.configs.length).val from by simp)
          (show (⟨a.val + 1, ha1_lt⟩ : Fin gc.configs.length).val < s.val from hgap)
      have ha1_nofire : ∀ k : Fin gc.configs.length,
          a1.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ t :=
        fun k hk1 hk2 => hno k (show a.val < k.val by simp [a1] at hk1; omega) hk2
      let phase : TernaryPhase gc t :=
        { a := a1, s := s, ha_lt_s := hgap, hs_mover := hs,
          ha_nonmover := ha1_nonmover, ht_nofire := ha1_nofire }
      -- normalForm → ¬isMechanismTriggering → not BothEven(0,0) → J+K ≥ 1
      have hnorm := hall_normal phase
      -- ifc on [a, s) = ifc on [a+1, s) for left/right t (step a fires t, not L or R)
      have hstepL : gc.intervalFireCount (left t) a.val (a.val + 1) = 0 := by
        rw [intervalFireCount_single gc (left t) a.isLt]
        simp [show gc.moverAt a ≠ left t from by rw [ha]; exact (left_ne_self_peb t).symm]
      have hstepR : gc.intervalFireCount (right t) a.val (a.val + 1) = 0 := by
        rw [intervalFireCount_single gc (right t) a.isLt]
        simp [show gc.moverAt a ≠ right t from by rw [ha]; exact (right_ne_self_peb t).symm]
      have hsplitL := intervalFireCount_split gc (left t)
        (show a.val ≤ a.val + 1 by omega) (show a.val + 1 ≤ s.val by omega)
      have hsplitR := intervalFireCount_split gc (right t)
        (show a.val ≤ a.val + 1 by omega) (show a.val + 1 ≤ s.val by omega)
      -- So ifc(L, a, s) = ifc(L, a+1, s) and ifc(R, a, s) = ifc(R, a+1, s)
      -- The phase has J = ifc(L, a+1, s), K = ifc(R, a+1, s)
      -- normalForm: ¬((Even J ∧ Even K) ∨ ...) so in particular ¬(Even J ∧ Even K)
      -- If J = 0 and K = 0 then both are even → contradiction with normalForm
      by_contra hlt
      push_neg at hlt
      -- hlt : ifc(L, a, s) + ifc(R, a, s) = 0
      have hsum0 : gc.intervalFireCount (left t) a.val s.val +
          gc.intervalFireCount (right t) a.val s.val = 0 := by omega
      have hJ0 : gc.intervalFireCount (left t) (a.val + 1) s.val = 0 := by omega
      have hK0 : gc.intervalFireCount (right t) (a.val + 1) s.val = 0 := by omega
      -- Both 0, hence both even
      have hphase_a : phase.a.val = a.val + 1 := rfl
      have hphase_s : phase.s.val = s.val := rfl
      have hJeven : Even (gc.intervalFireCount (left t) phase.a.val phase.s.val) :=
        ⟨0, by rw [hphase_a, hphase_s]; omega⟩
      have hKeven : Even (gc.intervalFireCount (right t) phase.a.val phase.s.val) :=
        ⟨0, by rw [hphase_a, hphase_s]; omega⟩
      -- This is BothEven, hence mechanism-triggering
      exact hnorm (Or.inl ⟨hJeven, hKeven⟩)
    · -- Empty gap: a+1 ≥ s. With has, s = a+1. Contradicts hno_consec.
      exact absurd (hno_consec a s has ha hs hno) hgap
  -- Step 2: Find the global min and max t-fire positions
  have hL_pos := gc.configs_length_pos
  let tFires : Finset (Fin gc.configs.length) :=
    Finset.univ.filter (fun k => gc.moverAt k = t)
  have htFires_ne : tFires.Nonempty := by
    have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc_t_ge2
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  let s_min : Fin gc.configs.length := tFires.min' htFires_ne
  let s_max : Fin gc.configs.length := tFires.max' htFires_ne
  have hs_min_fire : gc.moverAt s_min = t :=
    (Finset.mem_filter.mp (Finset.min'_mem tFires htFires_ne)).2
  have hs_max_fire : gc.moverAt s_max = t :=
    (Finset.mem_filter.mp (Finset.max'_mem tFires htFires_ne)).2
  have hs_ne : s_min ≠ s_max := by
    intro heq
    have huniq : ∀ k ∈ tFires, k = s_min := by
      intro k hk
      have hle1 : s_min ≤ k := Finset.min'_le tFires k hk
      have hle2 : k ≤ s_max := Finset.le_max' tFires k hk
      rw [← heq] at hle2; exact le_antisymm hle2 hle1
    have hfc_le1 : gc.fireCount t ≤ 1 := by
      rw [gc.fireCount_eq_sum_moverAt t]
      have hbd : ∀ j : Fin gc.configs.length,
          (if gc.moverAt j = t then (1 : Nat) else 0) ≤
            (if j = s_min then 1 else 0) := by
        intro j; by_cases hj : gc.moverAt j = t
        · rw [huniq j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)]; simp [hs_min_fire]
        · simp [hj]
      calc ∑ j, (if gc.moverAt j = t then (1 : Nat) else 0)
          ≤ ∑ j, (if j = s_min then 1 else 0) :=
            Finset.sum_le_sum (fun j _ => hbd j)
        _ = 1 := by rw [Finset.sum_eq_single s_min
              (fun b _ hb => by simp [hb]) (by simp)]; simp
    omega
  have hs_lt : s_min.val < s_max.val := by
    have hle : s_min ≤ s_max := Finset.min'_le tFires s_max (Finset.max'_mem tFires htFires_ne)
    exact lt_of_le_of_ne hle (fun h => hs_ne (Fin.ext h))
  -- Step 3: Apply ifc_sum_ge_of_consec_ge1 on [s_min, s_max]
  have hinterior := ifc_sum_ge_of_consec_ge1 gc t (left t) (right t) hall_ge1
    (s_max.val - s_min.val) s_min s_max le_rfl hs_lt hs_min_fire hs_max_fire
  -- Step 4: ifc(t, s_min, s_max) = fc(t) - 1
  -- (all t-fires except s_max fall in [s_min, s_max))
  have hifc_t_before : gc.intervalFireCount t 0 s_min.val = 0 := by
    apply intervalFireCount_eq_zero_of_noFire gc t (Nat.zero_le _)
      (Nat.le_of_lt s_min.isLt)
    intro k hk1 hk2 hfire
    have hk_mem : k ∈ tFires := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hfire⟩
    have := Finset.min'_le tFires k hk_mem; omega
  have hifc_t_after : gc.intervalFireCount t s_max.val gc.configs.length = 1 := by
    have h1 : gc.intervalFireCount t s_max.val (s_max.val + 1) = 1 := by
      rw [intervalFireCount_single gc t s_max.isLt]; simp [hs_max_fire]
    have h0 : gc.intervalFireCount t (s_max.val + 1) gc.configs.length = 0 := by
      apply intervalFireCount_eq_zero_of_noFire gc t (by omega) le_rfl
      intro k hk1 hk2 hfire
      have hk_mem : k ∈ tFires := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hfire⟩
      have := Finset.le_max' tFires k hk_mem; omega
    have := intervalFireCount_split gc t (show s_max.val ≤ s_max.val + 1 by omega)
      (show s_max.val + 1 ≤ gc.configs.length by omega)
    omega
  have hifc_t_mid : gc.intervalFireCount t s_min.val s_max.val = gc.fireCount t - 1 := by
    have hfull := fireCount_eq_intervalFireCount_full gc t
    have split_mid := intervalFireCount_split gc t (show s_min.val ≤ s_max.val by omega)
      (show s_max.val ≤ gc.configs.length from Nat.le_of_lt s_max.isLt)
    have split_all := intervalFireCount_split gc t (Nat.zero_le s_min.val)
      (show s_min.val ≤ gc.configs.length from Nat.le_of_lt s_min.isLt)
    rw [← hfull, split_mid] at split_all; omega
  -- Step 5: fc(L)+fc(R) ≥ sum(s_min, s_max) ≥ ifc(t, s_min, s_max) = fc(t)-1
  have hfc_sum_ge_interior :
      gc.fireCount (left t) + gc.fireCount (right t) ≥ gc.fireCount t - 1 := by
    have hfc_L_ge : gc.intervalFireCount (left t) s_min.val s_max.val ≤
        gc.fireCount (left t) := by
      have hfull := fireCount_eq_intervalFireCount_full gc (left t)
      have h1 := intervalFireCount_split gc (left t) (Nat.zero_le s_min.val)
        (show s_min.val ≤ gc.configs.length from Nat.le_of_lt s_min.isLt)
      have h2 := intervalFireCount_split gc (left t) (show s_min.val ≤ s_max.val by omega)
        (show s_max.val ≤ gc.configs.length from Nat.le_of_lt s_max.isLt)
      omega
    have hfc_R_ge : gc.intervalFireCount (right t) s_min.val s_max.val ≤
        gc.fireCount (right t) := by
      have hfull := fireCount_eq_intervalFireCount_full gc (right t)
      have h1 := intervalFireCount_split gc (right t) (Nat.zero_le s_min.val)
        (show s_min.val ≤ gc.configs.length from Nat.le_of_lt s_min.isLt)
      have h2 := intervalFireCount_split gc (right t) (show s_min.val ≤ s_max.val by omega)
        (show s_max.val ≤ gc.configs.length from Nat.le_of_lt s_max.isLt)
      omega
    rw [hifc_t_mid] at hinterior; omega
  -- Step 6: Parity upgrade. fc(L)+fc(R) is even (both binary).
  have heven_sum : Even (gc.fireCount (left t) + gc.fireCount (right t)) := by
    exact Even.add (gc.binary_fireCount_even (left t) hbL)
                   (gc.binary_fireCount_even (right t) hbR)
  -- If fc(t) is even: fc(t)-1 is odd, even sum ≥ odd → sum ≥ odd+1 = fc(t).
  -- If fc(t) is odd: fc(t)-1 is even, could have sum = fc(t)-1. Need wrap.
  by_cases heven_t : Even (gc.fireCount t)
  · -- fc(t) even: fc(L)+fc(R) ≥ fc(t)-1 (odd) and is even → ≥ fc(t)
    obtain ⟨k, hk⟩ := heven_t
    obtain ⟨m, hm⟩ := heven_sum
    omega
  · -- fc(t) odd: need wrap contribution ≥ 1.
    -- The wrap phase [0, s_min) ∪ [s_max+1, L) has no t-fires.
    -- Step 6a: wrap is nonempty (from hno_cyclic_consec).
    -- If s_min = 0 and s_max = L-1: step L-1 fires t, step 0 = (L-1+1)%L fires t,
    -- contradicting hno_cyclic_consec.
    have hwrap_nonempty : s_min.val > 0 ∨ s_max.val + 1 < gc.configs.length := by
      by_contra h; push_neg at h
      have hs_min_0 : s_min.val = 0 := by omega
      have hs_max_last : s_max.val = gc.configs.length - 1 := by omega
      have hmod : (s_max.val + 1) % gc.configs.length = 0 := by
        rw [hs_max_last]; exact Nat.succ_pred_eq_of_pos hL_pos ▸ Nat.mod_self _
      have hcontra := hno_cyclic_consec s_max hs_max_fire
      rw [show (⟨(s_max.val + 1) % gc.configs.length,
        Nat.mod_lt _ gc.configs_length_pos⟩ : Fin gc.configs.length) =
        ⟨0, hL_pos⟩ from Fin.ext hmod] at hcontra
      have hs_min_eq : s_min = ⟨0, hL_pos⟩ := Fin.ext hs_min_0
      rw [← hs_min_eq] at hcontra
      exact hcontra hs_min_fire
    -- Step 6b: wrap contribution ≥ 1. If wrap(L) + wrap(R) = 0, derive EC.
    -- Define wrap fire counts
    have hwrap_L := wrap_ifc_eq gc (left t) s_min.isLt s_max.isLt (Nat.le_of_lt hs_lt)
    have hwrap_R := wrap_ifc_eq gc (right t) s_min.isLt s_max.isLt (Nat.le_of_lt hs_lt)
    -- We need: fc(L) + fc(R) ≥ ifc(L, s_min, s_max+1) + ifc(R, s_min, s_max+1)
    --                         + wrap(L) + wrap(R)
    -- And wrap(L) + wrap(R) ≥ 1.
    -- By contradiction: assume wrap = 0 → EC → False.
    suffices hwrap_ge1 :
        gc.intervalFireCount (left t) 0 s_min.val +
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length +
        gc.intervalFireCount (right t) 0 s_min.val +
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length ≥ 1 by
      -- Combine: fc(L) + fc(R) = interior + wrap ≥ (fc(t)-1) + 1 = fc(t)
      -- fc(L) = ifc(L,0,s_min) + ifc(L,s_min,s_max) + ifc(L,s_max,s_max+1) + ifc(L,s_max+1,CL)
      -- ifc(L,s_max,s_max+1) = 0 (step s_max fires t ≠ L), so:
      -- fc(L) = ifc(L,0,s_min) + ifc(L,s_min,s_max) + ifc(L,s_max+1,CL)
      -- Similarly for fc(R). Total = wrap + interior.
      have hstep_smax_L : gc.intervalFireCount (left t) s_max.val (s_max.val + 1) = 0 := by
        rw [intervalFireCount_single gc (left t) s_max.isLt]
        simp [show gc.moverAt s_max ≠ left t from by
          rw [hs_max_fire]; exact (left_ne_self_peb t).symm]
      have hstep_smax_R : gc.intervalFireCount (right t) s_max.val (s_max.val + 1) = 0 := by
        rw [intervalFireCount_single gc (right t) s_max.isLt]
        simp [show gc.moverAt s_max ≠ right t from by
          rw [hs_max_fire]; exact (right_ne_self_peb t).symm]
      -- Decompose fc(L)
      have hfc_L_decomp : gc.fireCount (left t) =
          gc.intervalFireCount (left t) 0 s_min.val +
          gc.intervalFireCount (left t) s_min.val s_max.val +
          gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length := by
        have hfull := fireCount_eq_intervalFireCount_full gc (left t)
        have h1 := intervalFireCount_split gc (left t) (Nat.zero_le s_min.val)
          (show s_min.val ≤ gc.configs.length from Nat.le_of_lt s_min.isLt)
        have h2 := intervalFireCount_split gc (left t)
          (show s_min.val ≤ s_max.val by omega)
          (show s_max.val ≤ gc.configs.length from Nat.le_of_lt s_max.isLt)
        have h3 := intervalFireCount_split gc (left t)
          (show s_max.val ≤ s_max.val + 1 by omega)
          (show s_max.val + 1 ≤ gc.configs.length by omega)
        omega
      have hfc_R_decomp : gc.fireCount (right t) =
          gc.intervalFireCount (right t) 0 s_min.val +
          gc.intervalFireCount (right t) s_min.val s_max.val +
          gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length := by
        have hfull := fireCount_eq_intervalFireCount_full gc (right t)
        have h1 := intervalFireCount_split gc (right t) (Nat.zero_le s_min.val)
          (show s_min.val ≤ gc.configs.length from Nat.le_of_lt s_min.isLt)
        have h2 := intervalFireCount_split gc (right t)
          (show s_min.val ≤ s_max.val by omega)
          (show s_max.val ≤ gc.configs.length from Nat.le_of_lt s_max.isLt)
        have h3 := intervalFireCount_split gc (right t)
          (show s_max.val ≤ s_max.val + 1 by omega)
          (show s_max.val + 1 ≤ gc.configs.length by omega)
        omega
      rw [hifc_t_mid] at hinterior
      rw [hfc_L_decomp, hfc_R_decomp]
      -- Now goal: (wrap_L + interior_L + tail_L) + (wrap_R + interior_R + tail_R) ≥ fc(t)
      -- hinterior : interior_L + interior_R ≥ fc(t) - 1
      -- hwrap_ge1 : wrap_L + tail_L + wrap_R + tail_R ≥ 1
      -- hfc_t_ge2 : fc(t) ≥ 2 (so fc(t) - 1 + 1 = fc(t))
      have : gc.fireCount t - 1 + 1 = gc.fireCount t := by omega
      omega
    -- Prove wrap ≥ 1 by contradiction: assume = 0, derive EC.
    by_contra hwrap_zero; push_neg at hwrap_zero
    have hLwrap_before : gc.intervalFireCount (left t) 0 s_min.val = 0 := by omega
    have hLwrap_after : gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length = 0 := by
      omega
    have hRwrap_before : gc.intervalFireCount (right t) 0 s_min.val = 0 := by omega
    have hRwrap_after : gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length = 0 := by
      omega
    -- No t fires in wrap either (s_min is first, s_max is last)
    have hTwrap_before := hifc_t_before  -- ifc(t, 0, s_min) = 0
    have hTwrap_after : gc.intervalFireCount t (s_max.val + 1) gc.configs.length = 0 := by
      have h1 : gc.intervalFireCount t s_max.val (s_max.val + 1) = 1 := by
        rw [intervalFireCount_single gc t s_max.isLt]; simp [hs_max_fire]
      have := intervalFireCount_split gc t (show s_max.val ≤ s_max.val + 1 by omega)
        (show s_max.val + 1 ≤ gc.configs.length by omega)
      omega
    -- Derive EC using the nonempty wrap.
    apply absurd _ hnoEC
    by_cases hs_min_pos : s_min.val > 0
    · -- Case s_min > 0: step (s_min - 1) is a nonmover in [0, s_min).
      -- No t/L/R fires at step (s_min - 1), so config(s_min) agrees on {L,t,R}.
      have hsm1_lt : s_min.val - 1 < gc.configs.length := by omega
      let sm1 : Fin gc.configs.length := ⟨s_min.val - 1, hsm1_lt⟩
      -- sm1 doesn't fire t
      have hsm1_ne_t : gc.moverAt sm1 ≠ t := by
        intro hfire
        have hmem : sm1 ∈ tFires := Finset.mem_filter.mpr ⟨Finset.mem_univ sm1, hfire⟩
        have hle := Finset.min'_le tFires sm1 hmem
        exact absurd (show sm1.val ≥ s_min.val from hle) (by simp [sm1]; omega)
      -- sm1 doesn't fire L (ifc(L, 0, s_min) = 0 and sm1 ∈ [0, s_min))
      have hsm1_val : sm1.val = s_min.val - 1 := rfl
      have hsm1_lt_smin : sm1.val < s_min.val := by rw [hsm1_val]; omega
      have hsm1_ne_L : gc.moverAt sm1 ≠ left t := by
        intro hfire
        have hsingle : gc.intervalFireCount (left t) sm1.val (sm1.val + 1) = 1 := by
          rw [intervalFireCount_single gc (left t) sm1.isLt]; simp [hfire]
        -- ifc(L, 0, s_min) ≥ ifc(L, sm1, sm1+1) = 1 since [sm1, sm1+1) ⊆ [0, s_min)
        have hsplit := intervalFireCount_split gc (left t)
          (show 0 ≤ sm1.val by omega) (show sm1.val ≤ s_min.val by omega)
        have hsplit2 := intervalFireCount_split gc (left t)
          (show sm1.val ≤ sm1.val + 1 by omega)
          (show sm1.val + 1 ≤ s_min.val by rw [hsm1_val]; omega)
        omega
      -- sm1 doesn't fire R (similarly)
      have hsm1_ne_R : gc.moverAt sm1 ≠ right t := by
        intro hfire
        have hsingle : gc.intervalFireCount (right t) sm1.val (sm1.val + 1) = 1 := by
          rw [intervalFireCount_single gc (right t) sm1.isLt]; simp [hfire]
        have hsplit := intervalFireCount_split gc (right t)
          (show 0 ≤ sm1.val by omega) (show sm1.val ≤ s_min.val by omega)
        have hsplit2 := intervalFireCount_split gc (right t)
          (show sm1.val ≤ sm1.val + 1 by omega)
          (show sm1.val + 1 ≤ s_min.val by rw [hsm1_val]; omega)
        omega
      -- nextIndex(sm1) = s_min
      have hnext : nextIndex gc.configs sm1 = s_min := by
        ext; simp [nextIndex, sm1]
        rw [show s_min.val - 1 + 1 = s_min.val from by omega]
        exact Nat.mod_eq_of_lt s_min.isLt
      -- config(s_min)(q) = config(sm1)(q) for q ∈ {L, t, R}
      -- state_eq_of_ne_moverAt: i ≠ moverAt k → config(nextIndex k)(i) = config(k)(i)
      have hctx_L : (gc.configs.get s_min) (left t) = (gc.configs.get sm1) (left t) := by
        have := gc.state_eq_of_ne_moverAt sm1 (left t) hsm1_ne_L.symm
        rw [hnext] at this; exact this
      have hctx_t : (gc.configs.get s_min) t = (gc.configs.get sm1) t := by
        have := gc.state_eq_of_ne_moverAt sm1 t hsm1_ne_t.symm
        rw [hnext] at this; exact this
      have hctx_R : (gc.configs.get s_min) (right t) = (gc.configs.get sm1) (right t) := by
        have := gc.state_eq_of_ne_moverAt sm1 (right t) hsm1_ne_R.symm
        rw [hnext] at this; exact this
      -- EC: s_min (mover for t) and sm1 (nonmover for t) with same context
      exact ⟨s_min, sm1, t, hs_min_fire, hsm1_ne_t, hctx_L, hctx_t, hctx_R⟩
    · -- Case s_min = 0: wrap_nonempty forces s_max + 1 < CL.
      push_neg at hs_min_pos
      have hs_min_0 : s_min.val = 0 := by omega
      have hs_max_lt : s_max.val + 1 < gc.configs.length := by
        rcases hwrap_nonempty with h | h
        · omega
        · exact h
      let sp1 : Fin gc.configs.length := ⟨s_max.val + 1, hs_max_lt⟩
      -- sp1 doesn't fire t
      have hsp1_ne_t : gc.moverAt sp1 ≠ t := by
        intro hfire
        have hmem : sp1 ∈ tFires := Finset.mem_filter.mpr ⟨Finset.mem_univ sp1, hfire⟩
        have hle : sp1.val ≤ s_max.val := Finset.le_max' tFires sp1 hmem
        have : sp1.val = s_max.val + 1 := rfl
        omega
      -- Use configVal_eq_of_cyclic_noFire for each of L, t, R
      -- with a = 0, b = s_max + 1
      have hs_min_fin : s_min = ⟨0, hL_pos⟩ := Fin.ext hs_min_0
      -- Helper: no q fires in [s_max+1, CL) for q ∈ {L, t, R}
      have hnofire_tail_L : ∀ k : Fin gc.configs.length,
          s_max.val + 1 ≤ k.val → gc.moverAt k ≠ left t := by
        intro k hk hfire
        have : gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length ≥ 1 := by
          have hsingle : gc.intervalFireCount (left t) k.val (k.val + 1) = 1 := by
            rw [intervalFireCount_single gc (left t) k.isLt]; simp [hfire]
          have h1 := intervalFireCount_split gc (left t)
            (show s_max.val + 1 ≤ k.val from hk)
            (show k.val ≤ gc.configs.length from Nat.le_of_lt k.isLt)
          have h2 := intervalFireCount_split gc (left t)
            (show k.val ≤ k.val + 1 by omega)
            (show k.val + 1 ≤ gc.configs.length by omega)
          omega
        omega
      have hnofire_tail_t : ∀ k : Fin gc.configs.length,
          s_max.val + 1 ≤ k.val → gc.moverAt k ≠ t := by
        intro k hk hfire
        have : gc.intervalFireCount t (s_max.val + 1) gc.configs.length ≥ 1 := by
          have hsingle : gc.intervalFireCount t k.val (k.val + 1) = 1 := by
            rw [intervalFireCount_single gc t k.isLt]; simp [hfire]
          have h1 := intervalFireCount_split gc t
            (show s_max.val + 1 ≤ k.val from hk)
            (show k.val ≤ gc.configs.length from Nat.le_of_lt k.isLt)
          have h2 := intervalFireCount_split gc t
            (show k.val ≤ k.val + 1 by omega)
            (show k.val + 1 ≤ gc.configs.length by omega)
          omega
        omega
      have hnofire_tail_R : ∀ k : Fin gc.configs.length,
          s_max.val + 1 ≤ k.val → gc.moverAt k ≠ right t := by
        intro k hk hfire
        have : gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length ≥ 1 := by
          have hsingle : gc.intervalFireCount (right t) k.val (k.val + 1) = 1 := by
            rw [intervalFireCount_single gc (right t) k.isLt]; simp [hfire]
          have h1 := intervalFireCount_split gc (right t)
            (show s_max.val + 1 ≤ k.val from hk)
            (show k.val ≤ gc.configs.length from Nat.le_of_lt k.isLt)
          have h2 := intervalFireCount_split gc (right t)
            (show k.val ≤ k.val + 1 by omega)
            (show k.val + 1 ≤ gc.configs.length by omega)
          omega
        omega
      -- No fires in [0, 0) = ∅ (vacuous)
      have hnofire_head : ∀ (q : Fin sys.rs.n) (k : Fin gc.configs.length),
          k.val < 0 → gc.moverAt k ≠ q := by
        intro _ k hk; omega
      -- config(sp1)(q) = config(0)(q) via cyclic transport
      have hctx_L : (gc.configs.get sp1) (left t) =
          (gc.configs.get ⟨0, hL_pos⟩) (left t) :=
        configVal_eq_of_cyclic_noFire gc (left t) 0 (s_max.val + 1) hL_pos hs_max_lt
          (Nat.zero_le _) hnofire_tail_L (fun k hk => hnofire_head _ k hk)
      have hctx_t : (gc.configs.get sp1) t =
          (gc.configs.get ⟨0, hL_pos⟩) t :=
        configVal_eq_of_cyclic_noFire gc t 0 (s_max.val + 1) hL_pos hs_max_lt
          (Nat.zero_le _) hnofire_tail_t (fun k hk => hnofire_head _ k hk)
      have hctx_R : (gc.configs.get sp1) (right t) =
          (gc.configs.get ⟨0, hL_pos⟩) (right t) :=
        configVal_eq_of_cyclic_noFire gc (right t) 0 (s_max.val + 1) hL_pos hs_max_lt
          (Nat.zero_le _) hnofire_tail_R (fun k hk => hnofire_head _ k hk)
      -- EC: step 0 (mover for t) and sp1 (nonmover for t) with same context
      rw [hs_min_fin] at hs_min_fire
      exact ⟨⟨0, hL_pos⟩, sp1, t, hs_min_fire, hsp1_ne_t,
        hctx_L.symm, hctx_t.symm, hctx_R.symm⟩

/-- Pigeonhole for Nat: if n values are each ≥ 0 and sum to k < n, some value is 0.
    This is pure arithmetic, no cycle infrastructure needed. -/
theorem exists_zero_of_sum_lt {n : Nat} (f : Fin n → Nat)
    (hsum : (∑ i : Fin n, f i) < n) :
    ∃ i : Fin n, f i = 0 := by
  by_contra hall; push_neg at hall
  have hge : ∀ i : Fin n, f i ≥ 1 := fun i => Nat.one_le_iff_ne_zero.mpr (hall i)
  have : n ≤ ∑ i : Fin n, f i := by
    calc n = ∑ _ : Fin n, 1 := by simp [Finset.sum_const]
      _ ≤ ∑ i : Fin n, f i := Finset.sum_le_sum (fun i _ => hge i)
  omega

/-- Pigeonhole for Nat: if sum = k and count > k, some value is 0. -/
theorem exists_zero_of_count_exceeds_sum {n : Nat} (f : Fin n → Nat)
    (hsum_eq : (∑ i : Fin n, f i) = k) (hn_gt : n > k) :
    ∃ i : Fin n, f i = 0 := by
  exact exists_zero_of_sum_lt f (by omega)

end LeanMn
