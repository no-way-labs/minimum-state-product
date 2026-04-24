/-
  NestedFirings.lean — Entry conflict via nested processor firings

  Core theorems (all sorry-free):
  1. `binary_fireCount_ge_two`: binary processor fires >= 2 times
  2. `exists_two_firing_steps`: explicit existence of two firing steps
  3. `exists_consecutive_firing_pair`: find consecutive firings
  4. `contiguous_run_entry_conflict`: run of p-fires + non-p step -> entry conflict
  5. `gap1_entry_conflict`: gap=1 tight bounce -> entry conflict
  6. `gap1_entry_conflict_wrap`: gap=1 wrapping -> entry conflict
-/
import LeanMn.LowerBound.EntryConflict.ProcMinGap
import LeanMn.LowerBound.FireCountNe

namespace LeanMn

variable {sys : System}

/-! ### Ring topology -/

private theorem left_ne_self_nf (p : Fin sys.rs.n) : left p ≠ p := by
  intro h
  have hval := congrArg Fin.val h
  simp only [left_val] at hval
  have hp := p.isLt
  have hn := sys.rs.n_ge_4
  by_cases h0 : p.val = 0
  · rw [h0] at hval
    simp only [Nat.zero_add] at hval
    rw [Nat.mod_eq_of_lt (show sys.rs.n - 1 < sys.rs.n by omega)] at hval
    omega
  · rw [show p.val + sys.rs.n - 1 = (p.val - 1) + sys.rs.n from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (show p.val - 1 < sys.rs.n by omega)] at hval
    omega

private theorem right_ne_self_nf (p : Fin sys.rs.n) : right p ≠ p := by
  intro h
  have hval := congrArg Fin.val h
  simp only [right_val] at hval
  have hp := p.isLt
  have hn := sys.rs.n_ge_4
  by_cases h1 : p.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt h1] at hval; omega
  · rw [show p.val + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega

/-! ### Binary fires >= 2 -/

/-- A binary processor with positive fire count fires at least 2 times.
    (Even fire count + ≠ 1 + > 0 → ≥ 2.) -/
theorem binary_fireCount_ge_two (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p) (hfc_pos : gc.fireCount p > 0) :
    gc.fireCount p ≥ 2 := by
  have heven := gc.binary_fireCount_even p hbin
  have hne1 := GoodCycle.fireCount_ne_one gc p
  obtain ⟨k, hk⟩ := heven
  omega

/-! ### Two firing steps -/

theorem exists_two_firing_steps (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p) (hfc_pos : gc.fireCount p > 0) :
    ∃ (a b : Fin gc.configs.length), a.val < b.val ∧
      gc.moverAt a = p ∧ gc.moverAt b = p := by
  -- fireCount > 0 and even → fireCount ≥ 2
  have heven := gc.binary_fireCount_even p hbin
  have hne1 := GoodCycle.fireCount_ne_one gc p
  obtain ⟨k, hk⟩ := heven
  have hge2 : gc.fireCount p ≥ 2 := by omega
  -- Extract first firing step
  have hexists1 : ∃ a : Fin gc.configs.length, gc.moverAt a = p := by
    by_contra hall; push_neg at hall
    have hzero : gc.fireCount p = 0 := by
      rw [gc.fireCount_eq_sum_moverAt p]
      apply Finset.sum_eq_zero
      intro j _
      simp [show gc.moverAt j ≠ p from hall j]
    omega
  obtain ⟨a, ha⟩ := hexists1
  -- Extract second firing step
  have hexists2 : ∃ b : Fin gc.configs.length, b ≠ a ∧ gc.moverAt b = p := by
    by_contra hall; push_neg at hall
    -- hall : ∀ b, b = a ∨ gc.moverAt b ≠ p (from push_neg on ¬∃ b, b ≠ a ∧ moverAt b = p)
    -- Actually: ∀ b, b ≠ a → gc.moverAt b ≠ p
    have hmov_unique : ∀ j : Fin gc.configs.length, gc.moverAt j = p → j = a := by
      intro j hj; by_contra hne; exact hall j hne hj
    have hle1 : gc.fireCount p ≤ 1 := by
      rw [gc.fireCount_eq_sum_moverAt p]
      have : ∀ j : Fin gc.configs.length,
          (if gc.moverAt j = p then (1 : Nat) else 0) ≤ (if j = a then 1 else 0) := by
        intro j
        by_cases hja : j = a
        · rw [hja]; simp [ha]
        · have : gc.moverAt j ≠ p := hall j hja
          simp [this]
      calc ∑ j : Fin gc.configs.length, (if gc.moverAt j = p then (1 : Nat) else 0)
          ≤ ∑ j : Fin gc.configs.length, (if j = a then (1 : Nat) else 0) :=
            Finset.sum_le_sum (fun j _ => this j)
        _ = 1 := by
            rw [Finset.sum_eq_single a
              (fun b _ hba => by simp [hba]) (by simp)]; simp
    omega
  obtain ⟨b, hne, hb⟩ := hexists2
  have hne_val : a.val ≠ b.val := fun h => hne (Fin.ext h).symm
  by_cases hab : a.val < b.val
  · exact ⟨a, b, hab, ha, hb⟩
  · exact ⟨b, a, by omega, hb, ha⟩

/-! ### Consecutive firing pair -/

theorem exists_consecutive_firing_pair (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (a b : Fin gc.configs.length) (hab : a.val < b.val)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p) :
    ∃ (a' b' : Fin gc.configs.length),
      a'.val < b'.val ∧
      gc.moverAt a' = p ∧ gc.moverAt b' = p ∧
      (∀ k : Fin gc.configs.length,
        a'.val < k.val → k.val < b'.val → gc.moverAt k ≠ p) := by
  suffices hmain : ∀ d : Nat, ∀ (a b : Fin gc.configs.length),
      b.val - a.val ≤ d → a.val < b.val →
      gc.moverAt a = p → gc.moverAt b = p →
      ∃ (a' b' : Fin gc.configs.length),
        a'.val < b'.val ∧ gc.moverAt a' = p ∧ gc.moverAt b' = p ∧
        (∀ k : Fin gc.configs.length,
          a'.val < k.val → k.val < b'.val → gc.moverAt k ≠ p) by
    exact hmain (b.val - a.val) a b le_rfl hab ha hb
  intro d
  induction d with
  | zero => intro a b hd hab; omega
  | succ d ih =>
    intro a b hd hab ha hb
    by_cases hno : ∀ k : Fin gc.configs.length,
        a.val < k.val → k.val < b.val → gc.moverAt k ≠ p
    · exact ⟨a, b, hab, ha, hb, hno⟩
    · push_neg at hno
      obtain ⟨k, hak, hkb, hk⟩ := hno
      exact ih k b (by omega) hkb hk hb

/-! ### Prefix fire count in a run -/

private theorem prefixFireCount_add_of_run
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (a t : Nat) (_ha : a < gc.configs.length) (hat : a ≤ t)
    (ht_le : t ≤ gc.configs.length)
    (hrun : ∀ k : Fin gc.configs.length,
      a ≤ k.val → k.val < t → gc.moverAt k = p) :
    gc.prefixFireCount p t = gc.prefixFireCount p a + (t - a) := by
  induction t with
  | zero =>
    have ha0 : a = 0 := by omega
    rw [ha0]; simp
  | succ t ih =>
    by_cases hat' : a = t + 1
    · rw [hat']; simp
    · have hat'' : a ≤ t := by omega
      have ht_le' : t ≤ gc.configs.length := by omega
      have ih' := ih hat'' ht_le' (fun k hk1 hk2 => hrun k hk1 (by omega))
      rw [gc.prefixFireCount_succ, ih']
      have ht_lt : t < gc.configs.length := by omega
      rw [gc.fireIndicator_of_lt p ht_lt]
      have hmov := hrun ⟨t, ht_lt⟩ hat'' (Nat.lt_succ_self t)
      simp only [hmov, ite_true]
      omega

/-! ### Contiguous run entry conflict -/

/-- **Core lemma.** If binary processor p fires at every step in [a, t) and does
    NOT fire at step t (with a+1 < t), there is an entry conflict at p. -/
theorem contiguous_run_entry_conflict
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p)
    (a : Nat) (ha : a < gc.configs.length)
    (t : Nat) (ht : t < gc.configs.length)
    (_hat : a < t) (hat2 : a + 1 < t)
    (ht_ne : gc.moverAt ⟨t, ht⟩ ≠ p)
    (hrun : ∀ k : Fin gc.configs.length,
      a ≤ k.val → k.val < t → gc.moverAt k = p) :
    hasEntryConflict gc := by
  have hne_lp := left_ne_self_nf (sys := sys) p
  have hne_rp := right_ne_self_nf (sys := sys) p
  -- Neighbors preserved from a to t
  have hL := configVal_eq_of_noFire_between gc (left p) a t (by omega) ht
    (fun k hk1 hk2 => by
      have hmov := hrun k hk1 hk2
      intro heq; rw [hmov] at heq; exact hne_lp heq.symm)
  have hR := configVal_eq_of_noFire_between gc (right p) a t (by omega) ht
    (fun k hk1 hk2 => by
      have hmov := hrun k hk1 hk2
      intro heq; rw [hmov] at heq; exact hne_rp heq.symm)
  -- Fire count of p in [a, t) = t - a
  have hfire_count := prefixFireCount_add_of_run gc p a t ha (by omega) (by omega) hrun
  by_cases heven : (t - a) % 2 = 0
  · -- Even: p's parity at a = p's parity at t
    have hparity : gc.prefixFireCount p a % 2 = gc.prefixFireCount p t % 2 := by
      rw [hfire_count]; omega
    have hS := binary_config_eq_of_prefix_parity gc p hbin ha ht hparity
    have ha_fires := hrun ⟨a, ha⟩ le_rfl (by omega)
    exact ⟨⟨a, ha⟩, ⟨t, ht⟩, p, ha_fires, ht_ne, hL, hS, hR⟩
  · -- Odd: p's parity at a+1 = p's parity at t
    have ha1_lt : a + 1 < gc.configs.length := by omega
    have hfire_a1 : gc.prefixFireCount p (a + 1) = gc.prefixFireCount p a + 1 := by
      rw [gc.prefixFireCount_succ, gc.fireIndicator_of_lt p ha]
      have ha_fires := hrun ⟨a, ha⟩ le_rfl (by omega)
      simp only [ha_fires, ite_true]
    have hparity : gc.prefixFireCount p (a + 1) % 2 = gc.prefixFireCount p t % 2 := by
      rw [hfire_count, hfire_a1]; omega
    have hS := binary_config_eq_of_prefix_parity gc p hbin ha1_lt ht hparity
    have hL' := configVal_eq_of_noFire_between gc (left p) (a + 1) t (by omega) ht
      (fun k hk1 hk2 => by
        have hmov := hrun k (by omega) hk2
        intro heq; rw [hmov] at heq; exact hne_lp heq.symm)
    have hR' := configVal_eq_of_noFire_between gc (right p) (a + 1) t (by omega) ht
      (fun k hk1 hk2 => by
        have hmov := hrun k (by omega) hk2
        intro heq; rw [hmov] at heq; exact hne_rp heq.symm)
    have ha1_fires := hrun ⟨a + 1, ha1_lt⟩ (show a ≤ a + 1 by omega) hat2
    exact ⟨⟨a + 1, ha1_lt⟩, ⟨t, ht⟩, p, ha1_fires, ht_ne, hL', hS, hR'⟩

/-! ### Gap = 1 entry conflict -/

/-- Gap=1 tight bounce: binary p fires at a and a+1, moverAt(a+2) ≠ p. -/
theorem gap1_entry_conflict
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p)
    (a : Fin gc.configs.length)
    (ha1_lt : a.val + 1 < gc.configs.length)
    (ha2_lt : a.val + 2 < gc.configs.length)
    (ha_fires : gc.moverAt a = p)
    (ha1_fires : gc.moverAt ⟨a.val + 1, ha1_lt⟩ = p)
    (ha2_ne : gc.moverAt ⟨a.val + 2, ha2_lt⟩ ≠ p) :
    hasEntryConflict gc := by
  apply contiguous_run_entry_conflict gc p hbin a.val a.isLt (a.val + 2) ha2_lt
    (by omega) (by omega) ha2_ne
  intro k hk1 hk2
  have hkv : k.val = a.val ∨ k.val = a.val + 1 := by omega
  rcases hkv with hkeq | hkeq
  · have hk_eq : k = a := Fin.ext hkeq; rw [hk_eq]; exact ha_fires
  · have hk_eq : k = ⟨a.val + 1, ha1_lt⟩ := Fin.ext hkeq; rw [hk_eq]; exact ha1_fires

/-! ### Gap = 1 wrapping -/

/-- Gap=1 wrapping: binary p fires at L-2 and L-1, moverAt(0) ≠ p. -/
theorem gap1_entry_conflict_wrap
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p)
    (a : Fin gc.configs.length)
    (ha1_lt : a.val + 1 < gc.configs.length)
    (ha2_eq : a.val + 2 = gc.configs.length)
    (ha_fires : gc.moverAt a = p)
    (ha1_fires : gc.moverAt ⟨a.val + 1, ha1_lt⟩ = p)
    (h0_ne : gc.moverAt ⟨0, gc.configs_length_pos⟩ ≠ p) :
    hasEntryConflict gc := by
  have hne_lp := left_ne_self_nf (sys := sys) p
  have hne_rp := right_ne_self_nf (sys := sys) p
  -- p's prefix fire count at a is even (fireCount = prefixFireCount(a) + 2, fireCount even)
  have hpfc_a_even : gc.prefixFireCount p a.val % 2 = 0 := by
    -- fireCount p = prefixFireCount(L) and L = a+2
    -- prefixFireCount(a+2) = prefixFireCount(a+1) + fireIndicator(a+1)
    --                       = prefixFireCount(a) + fireIndicator(a) + fireIndicator(a+1)
    --                       = prefixFireCount(a) + 1 + 1
    have hstep1 : gc.prefixFireCount p (a.val + 1) = gc.prefixFireCount p a.val + 1 := by
      rw [gc.prefixFireCount_succ, gc.fireIndicator_of_lt p a.isLt]
      have : (⟨a.val, a.isLt⟩ : Fin gc.configs.length) = a := Fin.ext rfl
      rw [this, ha_fires]; simp
    have hstep2 : gc.prefixFireCount p (a.val + 2) = gc.prefixFireCount p (a.val + 1) + 1 := by
      rw [show a.val + 2 = (a.val + 1) + 1 from by omega,
          gc.prefixFireCount_succ, gc.fireIndicator_of_lt p ha1_lt, ha1_fires]; simp
    have hfc : gc.fireCount p = gc.prefixFireCount p a.val + 2 := by
      have : gc.fireCount p = gc.prefixFireCount p (a.val + 2) := by
        unfold GoodCycle.fireCount; congr 1; exact ha2_eq.symm
      rw [this, hstep2, hstep1]
    obtain ⟨m, hm⟩ := gc.binary_fireCount_even p hbin
    omega
  -- Same parity at 0 (prefixFireCount(0) = 0 ≡ 0 mod 2)
  have hparity : gc.prefixFireCount p a.val % 2 = gc.prefixFireCount p 0 % 2 := by
    rw [hpfc_a_even]; simp
  have hS := binary_config_eq_of_prefix_parity gc p hbin a.isLt gc.configs_length_pos hparity
  -- Left neighbor: value preserved from a through the wrap to 0
  -- At step a: moverAt = p ≠ left p, so left p unchanged
  -- At step a+1: moverAt = p ≠ left p, so left p unchanged
  -- config[nextIndex(a+1)] = config[0] (wrapping), and left p unchanged at both steps
  have hL : (gc.configs.get a) (left p) =
      (gc.configs.get ⟨0, gc.configs_length_pos⟩) (left p) := by
    -- Step 1: config[a](left p) = config[a+1](left p) because mover at a is p
    have h1 : (gc.configs.get a) (left p) =
        (gc.configs.get (nextIndex gc.configs a)) (left p) :=
      (gc.state_eq_of_ne_moverAt a (left p)
        (show left p ≠ gc.moverAt a by rw [ha_fires]; exact hne_lp)).symm
    -- nextIndex a = a+1 since a+1 < L
    have hnext_a : nextIndex gc.configs a = ⟨a.val + 1, ha1_lt⟩ := by
      apply Fin.ext; simp [nextIndex, Nat.mod_eq_of_lt ha1_lt]
    rw [hnext_a] at h1
    -- Step 2: config[a+1](left p) = config[nextIndex(a+1)](left p)
    have h2 : (gc.configs.get ⟨a.val + 1, ha1_lt⟩) (left p) =
        (gc.configs.get (nextIndex gc.configs ⟨a.val + 1, ha1_lt⟩)) (left p) :=
      (gc.state_eq_of_ne_moverAt ⟨a.val + 1, ha1_lt⟩ (left p)
        (show left p ≠ gc.moverAt ⟨a.val + 1, ha1_lt⟩ by rw [ha1_fires]; exact hne_lp)).symm
    -- nextIndex(a+1) = 0 since a+2 = L
    have hnext_a1 : nextIndex gc.configs ⟨a.val + 1, ha1_lt⟩ = ⟨0, gc.configs_length_pos⟩ := by
      apply Fin.ext; simp [nextIndex]; rw [show a.val + 1 + 1 = a.val + 2 from by omega, ha2_eq, Nat.mod_self]
    rw [hnext_a1] at h2
    exact h1.trans h2
  -- Right neighbor: same
  have hR : (gc.configs.get a) (right p) =
      (gc.configs.get ⟨0, gc.configs_length_pos⟩) (right p) := by
    have h1 : (gc.configs.get a) (right p) =
        (gc.configs.get (nextIndex gc.configs a)) (right p) :=
      (gc.state_eq_of_ne_moverAt a (right p)
        (show right p ≠ gc.moverAt a by rw [ha_fires]; exact hne_rp)).symm
    have hnext_a : nextIndex gc.configs a = ⟨a.val + 1, ha1_lt⟩ := by
      apply Fin.ext; simp [nextIndex, Nat.mod_eq_of_lt ha1_lt]
    rw [hnext_a] at h1
    have h2 : (gc.configs.get ⟨a.val + 1, ha1_lt⟩) (right p) =
        (gc.configs.get (nextIndex gc.configs ⟨a.val + 1, ha1_lt⟩)) (right p) :=
      (gc.state_eq_of_ne_moverAt ⟨a.val + 1, ha1_lt⟩ (right p)
        (show right p ≠ gc.moverAt ⟨a.val + 1, ha1_lt⟩ by rw [ha1_fires]; exact hne_rp)).symm
    have hnext_a1 : nextIndex gc.configs ⟨a.val + 1, ha1_lt⟩ = ⟨0, gc.configs_length_pos⟩ := by
      apply Fin.ext; simp [nextIndex]; rw [show a.val + 1 + 1 = a.val + 2 from by omega, ha2_eq, Nat.mod_self]
    rw [hnext_a1] at h2
    exact h1.trans h2
  exact ⟨a, ⟨0, gc.configs_length_pos⟩, p, ha_fires, h0_ne, hL, hS, hR⟩

end LeanMn
