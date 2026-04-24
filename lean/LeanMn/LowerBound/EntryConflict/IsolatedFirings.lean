/-
  IsolatedFirings.lean — Binary isolated firings or entry conflict

  Core theorem (binary_isolated_firings_or_ec):
  A binary processor with fireCount >= 2 either causes an entry conflict,
  fires at every step, or has only isolated firings (no consecutive pair).
-/
import LeanMn.LowerBound.EntryConflict.NestedFirings

namespace LeanMn

variable {sys : System}

/-! ### Ring topology -/

private theorem left_ne_self_if (p : Fin sys.rs.n) : left p ≠ p := by
  intro h
  have hval := congrArg Fin.val h
  simp only [left_val] at hval
  have hp := p.isLt; have hn := sys.rs.n_ge_4
  by_cases h0 : p.val = 0
  · rw [h0] at hval; simp only [Nat.zero_add] at hval
    rw [Nat.mod_eq_of_lt (show sys.rs.n - 1 < sys.rs.n by omega)] at hval; omega
  · rw [show p.val + sys.rs.n - 1 = (p.val - 1) + sys.rs.n from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (show p.val - 1 < sys.rs.n by omega)] at hval
    omega

private theorem right_ne_self_if (p : Fin sys.rs.n) : right p ≠ p := by
  intro h
  have hval := congrArg Fin.val h
  simp only [right_val] at hval
  have hp := p.isLt; have hn := sys.rs.n_ge_4
  by_cases h1 : p.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt h1] at hval; omega
  · rw [show p.val + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega

/-! ### Helper: nextIndex arithmetic -/

private theorem nextIndex_val_succ {gc : GoodCycle sys} {k : Nat}
    (hk : k < gc.configs.length) (hk1 : k + 1 < gc.configs.length) :
    nextIndex gc.configs ⟨k, hk⟩ = ⟨k + 1, hk1⟩ :=
  Fin.ext (by simp [nextIndex, Nat.mod_eq_of_lt hk1])

private theorem nextIndex_val_wrap {gc : GoodCycle sys} {k : Nat}
    (hk : k < gc.configs.length) (hk_last : k + 1 = gc.configs.length) :
    nextIndex gc.configs ⟨k, hk⟩ = ⟨0, gc.configs_length_pos⟩ :=
  Fin.ext (by simp [nextIndex, hk_last, Nat.mod_self])

/-! ### Wrap-pair entry conflict -/

/-- If binary p fires at L-1 and 0, doesn't fire at 1, and L >= 3: entry conflict. -/
private theorem wrap_pair_ec
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p)
    (hL3 : 3 ≤ gc.configs.length)
    (hmL1 : gc.moverAt ⟨gc.configs.length - 1, by omega⟩ = p)
    (hm0 : gc.moverAt ⟨0, gc.configs_length_pos⟩ = p)
    (hm1_ne : gc.moverAt ⟨1, by omega⟩ ≠ p) :
    hasEntryConflict gc := by
  set L := gc.configs.length
  have hne_lp := left_ne_self_if (sys := sys) p
  have hne_rp := right_ne_self_if (sys := sys) p
  have hL1_lt : L - 1 < L := by omega
  have h1_lt : (1 : Nat) < L := by omega
  have hnL1 := nextIndex_val_wrap (gc := gc) hL1_lt (by omega)
  have hn0 := nextIndex_val_succ (gc := gc) gc.configs_length_pos h1_lt
  -- Left p preserved: L-1 → 0 → 1
  have hL_eq : (gc.configs.get ⟨L - 1, hL1_lt⟩) (left p) =
      (gc.configs.get ⟨1, h1_lt⟩) (left p) := by
    have h1 := gc.state_eq_of_ne_moverAt ⟨L - 1, hL1_lt⟩ (left p)
      (show left p ≠ gc.moverAt ⟨L - 1, hL1_lt⟩ by rw [hmL1]; exact hne_lp)
    rw [hnL1] at h1
    have h2 := gc.state_eq_of_ne_moverAt ⟨0, gc.configs_length_pos⟩ (left p)
      (show left p ≠ gc.moverAt ⟨0, gc.configs_length_pos⟩ by rw [hm0]; exact hne_lp)
    rw [hn0] at h2
    exact h1.symm.trans h2.symm
  -- Right p preserved: L-1 → 0 → 1
  have hR_eq : (gc.configs.get ⟨L - 1, hL1_lt⟩) (right p) =
      (gc.configs.get ⟨1, h1_lt⟩) (right p) := by
    have h1 := gc.state_eq_of_ne_moverAt ⟨L - 1, hL1_lt⟩ (right p)
      (show right p ≠ gc.moverAt ⟨L - 1, hL1_lt⟩ by rw [hmL1]; exact hne_rp)
    rw [hnL1] at h1
    have h2 := gc.state_eq_of_ne_moverAt ⟨0, gc.configs_length_pos⟩ (right p)
      (show right p ≠ gc.moverAt ⟨0, gc.configs_length_pos⟩ by rw [hm0]; exact hne_rp)
    rw [hn0] at h2
    exact h1.symm.trans h2.symm
  -- Binary parity: config[1](p) = config[L-1](p)
  have hpfc1 : gc.prefixFireCount p 1 = 1 := by
    rw [gc.prefixFireCount_succ, gc.prefixFireCount_zero,
        gc.fireIndicator_of_lt p gc.configs_length_pos, hm0]; simp
  have hpfcL1 : gc.prefixFireCount p (L - 1) = gc.fireCount p - 1 := by
    have hstep : gc.prefixFireCount p L = gc.prefixFireCount p (L - 1) +
        gc.fireIndicator p (L - 1) := by
      conv_lhs => rw [show L = (L - 1) + 1 from by omega]
      exact gc.prefixFireCount_succ p (L - 1)
    have hind : gc.fireIndicator p (L - 1) = 1 := by
      rw [gc.fireIndicator_of_lt p hL1_lt, hmL1]; simp
    unfold GoodCycle.fireCount; rw [hstep, hind]; omega
  have hparity : gc.prefixFireCount p 1 % 2 = gc.prefixFireCount p (L - 1) % 2 := by
    rw [hpfc1, hpfcL1]
    -- Goal: 1 % 2 = (gc.fireCount p - 1) % 2
    -- fireCount is even, say 2*m. So (2*m - 1) % 2 = 1 % 2.
    obtain ⟨mm, hmm⟩ := gc.binary_fireCount_even p hbin
    rw [hmm]
    -- Goal: 1 % 2 = (2 * mm - 1) % 2 ... but Nat subtraction is tricky
    -- If mm = 0: 2*0 - 1 = 0, 0 % 2 = 0 ≠ 1. But fireCount ≥ 2 (from hL3, since p fires
    -- at L-1 and 0, two distinct steps). Actually we don't have hfc here but we do know
    -- L ≥ 3, hmL1, hm0. So fireCount ≥ 2. Thus mm ≥ 1.
    -- Actually we can prove mm ≥ 1 from the fact that two distinct steps fire p.
    have hmm_pos : mm ≥ 1 := by
      by_contra h; push_neg at h
      have : mm = 0 := by omega
      rw [this] at hmm; simp at hmm
      -- fireCount = 0 but p fires at step 0 and L-1
      have hfc_pos : gc.fireCount p ≥ 1 := by
        unfold GoodCycle.fireCount GoodCycle.prefixFireCount
        have : gc.fireIndicator p 0 = 1 := by
          rw [gc.fireIndicator_of_lt p gc.configs_length_pos, hm0]; simp
        have h0 : 0 ∈ Finset.range gc.configs.length := Finset.mem_range.mpr gc.configs_length_pos
        calc ∑ k ∈ Finset.range gc.configs.length, gc.fireIndicator p k
            ≥ gc.fireIndicator p 0 := Finset.single_le_sum (fun _ _ => Nat.zero_le _) h0
          _ = 1 := this
      omega
    omega
  have hS_eq := binary_config_eq_of_prefix_parity gc p hbin h1_lt hL1_lt hparity
  -- Entry conflict: k₁ = L-1 (mover), k₂ = 1 (non-mover)
  exact ⟨⟨L - 1, hL1_lt⟩, ⟨1, h1_lt⟩, p, hmL1, hm1_ne, hL_eq, hS_eq.symm, hR_eq⟩

/-! ### Wrapping run entry conflict -/

/-- Sum of fireIndicator over [a, L) when all steps fire p. -/
private theorem fireIndicator_sum_run
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (a : Nat) (ha : a < gc.configs.length)
    (hrun : ∀ (j : Nat), a ≤ j → (hj : j < gc.configs.length) → gc.moverAt ⟨j, hj⟩ = p) :
    gc.fireCount p = gc.prefixFireCount p a + (gc.configs.length - a) := by
  unfold GoodCycle.fireCount GoodCycle.prefixFireCount
  rw [show gc.configs.length = a + (gc.configs.length - a) from by omega,
      Finset.sum_range_add]
  congr 1
  have : ∀ j ∈ Finset.range (gc.configs.length - a),
      gc.fireIndicator p (a + j) = 1 := by
    intro j hj
    have hjr := Finset.mem_range.mp hj
    have haj : a + j < gc.configs.length := by omega
    rw [gc.fireIndicator_of_lt p haj, hrun (a + j) (by omega) haj]; simp
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range]; simp

/-- If p fires at all steps [a, L) with L-a >= 2, and moverAt(0) ≠ p: entry conflict. -/
private theorem wrap_run_ec
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p)
    (a : Nat) (ha : a < gc.configs.length)
    (ha1 : a + 1 < gc.configs.length)
    (hrun : ∀ (j : Nat), a ≤ j → (hj : j < gc.configs.length) → gc.moverAt ⟨j, hj⟩ = p)
    (hm0_ne : gc.moverAt ⟨0, gc.configs_length_pos⟩ ≠ p) :
    hasEntryConflict gc := by
  set L := gc.configs.length
  have hne_lp := left_ne_self_if (sys := sys) p
  have hne_rp := right_ne_self_if (sys := sys) p
  have hL1_lt : L - 1 < L := by omega
  have hma := hrun a le_rfl ha
  have hma1 := hrun (a + 1) (by omega) ha1
  have hmL1 := hrun (L - 1) (by omega) hL1_lt
  have hnL1 := nextIndex_val_wrap (gc := gc) hL1_lt (by omega : L - 1 + 1 = L)
  -- Neighbors: a → L-1 (no fire of left/right), L-1 → 0 (p fires, preserves left/right)
  have hLa_L1 := configVal_eq_of_noFire_between gc (left p) a (L - 1) (by omega) hL1_lt
    (fun ⟨j, hj⟩ haj hjL => by
      intro heq; rw [hrun j (by exact haj) hj] at heq; exact hne_lp heq.symm)
  have hL_wrap := gc.state_eq_of_ne_moverAt ⟨L - 1, hL1_lt⟩ (left p)
    (show left p ≠ gc.moverAt ⟨L - 1, hL1_lt⟩ by rw [hmL1]; exact hne_lp)
  rw [hnL1] at hL_wrap
  have hRa_L1 := configVal_eq_of_noFire_between gc (right p) a (L - 1) (by omega) hL1_lt
    (fun ⟨j, hj⟩ haj hjL => by
      intro heq; rw [hrun j (by exact haj) hj] at heq; exact hne_rp heq.symm)
  have hR_wrap := gc.state_eq_of_ne_moverAt ⟨L - 1, hL1_lt⟩ (right p)
    (show right p ≠ gc.moverAt ⟨L - 1, hL1_lt⟩ by rw [hmL1]; exact hne_rp)
  rw [hnL1] at hR_wrap
  -- Combined: config[a](left/right p) = config[0](left/right p)
  have hL_a_0 := hLa_L1.trans hL_wrap.symm
  have hR_a_0 := hRa_L1.trans hR_wrap.symm
  -- Parity
  have hfire_sum := fireIndicator_sum_run gc p a ha hrun
  obtain ⟨m, hm⟩ := gc.binary_fireCount_even p hbin
  have hpfc_a1 : gc.prefixFireCount p (a + 1) = gc.prefixFireCount p a + 1 := by
    rw [gc.prefixFireCount_succ, gc.fireIndicator_of_lt p ha, hma]; simp
  have hpfc0 : gc.prefixFireCount p 0 = 0 := gc.prefixFireCount_zero p
  by_cases hparity : (L - a) % 2 = 0
  · -- Even: config[a](p) = config[0](p)
    have hp : gc.prefixFireCount p a % 2 = gc.prefixFireCount p 0 % 2 := by
      rw [hpfc0]; omega
    have hS := binary_config_eq_of_prefix_parity gc p hbin ha gc.configs_length_pos hp
    exact ⟨⟨a, ha⟩, ⟨0, gc.configs_length_pos⟩, p, hma, hm0_ne, hL_a_0, hS, hR_a_0⟩
  · -- Odd: config[a+1](p) = config[0](p)
    have hp : gc.prefixFireCount p (a + 1) % 2 = gc.prefixFireCount p 0 % 2 := by
      rw [hpfc0, hpfc_a1]; omega
    have hS := binary_config_eq_of_prefix_parity gc p hbin ha1 gc.configs_length_pos hp
    -- Neighbors at a+1 = neighbors at a (mover at a is p)
    have hna := nextIndex_val_succ (gc := gc) ha ha1
    have hLa1 := gc.state_eq_of_ne_moverAt ⟨a, ha⟩ (left p)
      (show left p ≠ gc.moverAt ⟨a, ha⟩ by rw [hma]; exact hne_lp)
    rw [hna] at hLa1
    have hRa1 := gc.state_eq_of_ne_moverAt ⟨a, ha⟩ (right p)
      (show right p ≠ gc.moverAt ⟨a, ha⟩ by rw [hma]; exact hne_rp)
    rw [hna] at hRa1
    exact ⟨⟨a + 1, ha1⟩, ⟨0, gc.configs_length_pos⟩, p, hma1, hm0_ne,
      hLa1.trans hL_a_0, hS, hRa1.trans hR_a_0⟩

/-! ### Non-wrapping run extension -/

/-- Extend run [a, a+d) forward. Either EC or p fires at all steps >= a. -/
private theorem extend_run_fwd
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p)
    (a : Nat) (ha : a < gc.configs.length)
    (d : Nat) (hd2 : 2 ≤ d) (had : a + d ≤ gc.configs.length)
    (hrun : ∀ (j : Nat), a ≤ j → j < a + d →
      (hj : j < gc.configs.length) → gc.moverAt ⟨j, hj⟩ = p) :
    hasEntryConflict gc ∨
    (∀ (j : Nat), a ≤ j → (hj : j < gc.configs.length) → gc.moverAt ⟨j, hj⟩ = p) := by
  by_cases had_eq : a + d = gc.configs.length
  · right; intro j haj hj; exact hrun j haj (by omega) hj
  · have had_lt : a + d < gc.configs.length := by omega
    by_cases hstep : gc.moverAt ⟨a + d, had_lt⟩ = p
    · have hrun' : ∀ (j : Nat), a ≤ j → j < a + (d + 1) →
          (hj : j < gc.configs.length) → gc.moverAt ⟨j, hj⟩ = p := by
        intro j haj hjd1 hj
        by_cases hjd : j < a + d
        · exact hrun j haj hjd hj
        · have hjeq : j = a + d := by omega
          subst hjeq; exact hstep
      exact extend_run_fwd gc p hbin a ha (d + 1) (by omega) (by omega) hrun'
    · left
      have hrun' : ∀ k : Fin gc.configs.length,
          a ≤ k.val → k.val < a + d → gc.moverAt k = p :=
        fun ⟨j, hj⟩ haj hjd => hrun j haj hjd hj
      exact contiguous_run_entry_conflict gc p hbin a ha (a + d) had_lt
        (by omega) (by omega) hstep hrun'
termination_by gc.configs.length - (a + d)

/-! ### Front extension -/

/-- Extend front [0, t) toward a. Either EC or p fires everywhere. Requires 0 < t. -/
private theorem extend_front
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p)
    (a : Nat) (ha_lt : a < gc.configs.length) (ha1_lt : a + 1 < gc.configs.length)
    (t : Nat) (ht_pos : 0 < t) (ht_le_a : t ≤ a)
    (hfront : ∀ (j : Nat), j < t → (hj : j < gc.configs.length) → gc.moverAt ⟨j, hj⟩ = p)
    (hback : ∀ (j : Nat), a ≤ j → (hj : j < gc.configs.length) → gc.moverAt ⟨j, hj⟩ = p) :
    hasEntryConflict gc ∨ (∀ k : Fin gc.configs.length, gc.moverAt k = p) := by
  by_cases ht_eq_a : t = a
  · -- Runs cover everything
    right; intro ⟨j, hj⟩
    by_cases hjlt : j < a
    · exact hfront j (by omega) hj
    · exact hback j (by omega) hj
  · have ht_lt : t < gc.configs.length := by omega
    by_cases hstep : gc.moverAt ⟨t, ht_lt⟩ = p
    · have hfront' : ∀ (j : Nat), j < t + 1 → (hj : j < gc.configs.length) →
          gc.moverAt ⟨j, hj⟩ = p := by
        intro j hj1 hj
        by_cases hjt : j < t
        · exact hfront j hjt hj
        · have hjeq : j = t := by omega
          subst hjeq; exact hstep
      exact extend_front gc p hbin a ha_lt ha1_lt (t + 1) (by omega) (by omega) hfront' hback
    · -- Front terminates at t.
      left
      by_cases ht2 : 2 ≤ t
      · exact contiguous_run_entry_conflict gc p hbin 0 gc.configs_length_pos t ht_lt
          (by omega) (by omega) hstep (fun ⟨j, hj⟩ _ hjt => hfront j hjt hj)
      · -- t = 1
        have ht1 : t = 1 := by omega
        subst ht1
        have hm1_ne : gc.moverAt ⟨1, by omega⟩ ≠ p := by
          convert hstep using 1
        exact wrap_pair_ec gc p hbin (by omega)
          (hback (gc.configs.length - 1) (by omega) (by omega))
          (hfront 0 (by omega) gc.configs_length_pos)
          hm1_ne
termination_by a - t

/-! ### Main theorem -/

/-- A binary processor that fires at two consecutive steps either causes
    an entry conflict or fires at every single step of the cycle. -/
theorem binary_consec_fires_ec_or_permanent
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p)
    (a : Nat) (ha : a < gc.configs.length)
    (ha1 : a + 1 < gc.configs.length)
    (hma : gc.moverAt ⟨a, ha⟩ = p)
    (hma1 : gc.moverAt ⟨a + 1, ha1⟩ = p) :
    hasEntryConflict gc ∨ (∀ k : Fin gc.configs.length, gc.moverAt k = p) := by
  -- Extend [a, a+2) forward
  have hrun2 : ∀ (j : Nat), a ≤ j → j < a + 2 →
      (hj : j < gc.configs.length) → gc.moverAt ⟨j, hj⟩ = p := by
    intro j haj hja2 hj
    have : j = a ∨ j = a + 1 := by omega
    rcases this with rfl | rfl
    · exact hma
    · exact hma1
  rcases extend_run_fwd gc p hbin a ha 2 le_rfl (by omega) hrun2 with hec | hfwd
  · exact Or.inl hec
  · by_cases ha0 : a = 0
    · right; intro ⟨j, hj⟩; exact hfwd j (by omega) hj
    · by_cases hm0 : gc.moverAt ⟨0, gc.configs_length_pos⟩ = p
      · exact extend_front gc p hbin a ha ha1 1 (by omega) (by omega)
          (fun j hj1 hj => by
            have hjeq : j = 0 := by omega
            subst hjeq; exact hm0)
          (fun j haj hj => hfwd j haj hj)
      · exact Or.inl (wrap_run_ec gc p hbin a ha ha1
          (fun j haj hj => hfwd j haj hj) hm0)

/-! ### Wrapping consecutive pair -/

/-- When binary p fires at L-1 and 0 (wrapping pair): EC or permanent. -/
private theorem wrap_consec_ec_or_permanent
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p)
    (hfc : 2 ≤ gc.fireCount p)
    (hmL1 : gc.moverAt ⟨gc.configs.length - 1,
      Nat.sub_lt gc.configs_length_pos Nat.one_pos⟩ = p)
    (hm0 : gc.moverAt ⟨0, gc.configs_length_pos⟩ = p) :
    hasEntryConflict gc ∨ (∀ k : Fin gc.configs.length, gc.moverAt k = p) := by
  have hL2 : 2 ≤ gc.configs.length := by
    have h1 := Finset.single_le_sum (f := gc.fireCount) (fun q _ => Nat.zero_le _)
      (Finset.mem_univ p)
    rw [gc.sum_fireCount] at h1; omega
  by_cases hL2_eq : gc.configs.length = 2
  · right; intro ⟨j, hj⟩
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · exact hm0
    · have h1eq : (⟨1, hj⟩ : Fin gc.configs.length) =
          ⟨gc.configs.length - 1, Nat.sub_lt gc.configs_length_pos Nat.one_pos⟩ :=
        Fin.ext (show (1 : Nat) = gc.configs.length - 1 by omega)
      rw [h1eq]; exact hmL1
  · have h1_lt : (1 : Nat) < gc.configs.length := by omega
    by_cases hm1 : gc.moverAt ⟨1, h1_lt⟩ = p
    · exact binary_consec_fires_ec_or_permanent gc p hbin 0 gc.configs_length_pos h1_lt hm0 hm1
    · exact Or.inl (wrap_pair_ec gc p hbin (by omega) hmL1 hm0 hm1)

/-! ### Corollary -/

/-- A binary processor with fireCount >= 2 either causes an entry conflict,
    fires at every step, or has only isolated firings (no consecutive pair). -/
theorem binary_isolated_firings_or_ec
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p) (hfc : 2 ≤ gc.fireCount p) :
    hasEntryConflict gc ∨
    (∀ k : Fin gc.configs.length, gc.moverAt k = p) ∨
    (∀ (a : Fin gc.configs.length),
      gc.moverAt a = p → gc.moverAt (nextIndex gc.configs a) ≠ p) := by
  by_cases hconsec : ∃ (a : Fin gc.configs.length),
      gc.moverAt a = p ∧ gc.moverAt (nextIndex gc.configs a) = p
  · obtain ⟨a, ha_p, ha1_p⟩ := hconsec
    by_cases ha1_lt : a.val + 1 < gc.configs.length
    · have hnext := nextIndex_val_succ (gc := gc) a.isLt ha1_lt
      rw [hnext] at ha1_p
      rcases binary_consec_fires_ec_or_permanent gc p hbin a.val a.isLt ha1_lt ha_p ha1_p
        with hec | hall
      · exact Or.inl hec
      · exact Or.inr (Or.inl hall)
    · have haeq : a.val = gc.configs.length - 1 := by have := a.isLt; omega
      have hnext := nextIndex_val_wrap (gc := gc) a.isLt (by omega)
      rw [hnext] at ha1_p
      have hmL1 : gc.moverAt ⟨gc.configs.length - 1,
          Nat.sub_lt gc.configs_length_pos Nat.one_pos⟩ = p := by
        have : a = ⟨gc.configs.length - 1, Nat.sub_lt gc.configs_length_pos Nat.one_pos⟩ :=
          Fin.ext haeq
        rw [← this]; exact ha_p
      rcases wrap_consec_ec_or_permanent gc p hbin hfc hmL1 ha1_p with hec | hall
      · exact Or.inl hec
      · exact Or.inr (Or.inl hall)
  · push_neg at hconsec
    exact Or.inr (Or.inr fun a ha_p => hconsec a ha_p)

end LeanMn
