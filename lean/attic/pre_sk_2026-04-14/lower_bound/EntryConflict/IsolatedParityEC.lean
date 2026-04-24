/-
  IsolatedParityEC.lean — Entry conflict for isolated binary firings with 3 consecutive binary

  When 3 consecutive binary {i, ri, rri} exist and ri = right i has all isolated
  firings (no two consecutive), the MinFiringGap for ri has gap >= 2.

  Key results:
  1. `exists_minFiringGap`: builds a MinFiringGap from fireCount >= 2.
  2. `prefixFireCount_eq_of_noFire_range`: value-level preservation when a processor
     doesn't fire in a range.
  3. `cross_gap_s_parity_match`: S-parity at b2+1 equals S-parity at b1 when ri
     fires at b1 and b2 with no fires in between.
  4. Parity preservation lemmas for L and R at ri firing steps.
  5. `cross_gap_ec`: entry conflict from cross-gap parity matching.
-/
import LeanMn.LowerBound.EntryConflict.ParityWalk

namespace LeanMn

variable {sys : System}

/-! ### MinFiringGap construction -/

/-- Any processor with fireCount >= 2 has a MinFiringGap (Prop-level existence). -/
theorem exists_minFiringGap_prop (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hfc : gc.fireCount p ≥ 2) :
    ∃ mg : MinFiringGap gc p, True := by
  -- Get two firing steps
  have hexists1 : ∃ a : Fin gc.configs.length, gc.moverAt a = p := by
    by_contra hall; push_neg at hall
    have hzero : gc.fireCount p = 0 := by
      rw [gc.fireCount_eq_sum_moverAt p]
      apply Finset.sum_eq_zero
      intro j _; simp [show gc.moverAt j ≠ p from hall j]
    omega
  obtain ⟨a, ha⟩ := hexists1
  have hexists2 : ∃ b : Fin gc.configs.length, b ≠ a ∧ gc.moverAt b = p := by
    by_contra hall; push_neg at hall
    have hle1 : gc.fireCount p ≤ 1 := by
      rw [gc.fireCount_eq_sum_moverAt p]
      calc ∑ j : Fin gc.configs.length, (if gc.moverAt j = p then (1 : Nat) else 0)
          ≤ ∑ j : Fin gc.configs.length, (if j = a then (1 : Nat) else 0) :=
            Finset.sum_le_sum (fun j _ => by
              by_cases hja : j = a
              · rw [hja]; simp [ha]
              · have : gc.moverAt j ≠ p := hall j hja; simp [this])
        _ = 1 := by
            rw [Finset.sum_eq_single a
              (fun b _ hba => by simp [hba]) (by simp)]; simp
    omega
  obtain ⟨b, hne, hb⟩ := hexists2
  have hab : a.val < b.val ∨ b.val < a.val := by omega
  rcases hab with hab | hba
  · obtain ⟨a', b', hab', ha', hb', hno'⟩ :=
      exists_consecutive_firing_pair gc p a b hab ha hb
    -- Build min gap
    let S : Finset (Fin gc.configs.length × Fin gc.configs.length) :=
      (Finset.univ ×ˢ Finset.univ).filter fun ⟨a'', b''⟩ =>
        gc.moverAt a'' = p ∧ gc.moverAt b'' = p ∧ a''.val < b''.val ∧
        (∀ k : Fin gc.configs.length, a''.val < k.val → k.val < b''.val → gc.moverAt k ≠ p)
    have hS_nonempty : S.Nonempty := by
      refine ⟨⟨a', b'⟩, ?_⟩
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      exact ⟨ha', hb', hab', hno'⟩
    obtain ⟨⟨a'', b''⟩, hmem, hmin⟩ :=
      Finset.exists_min_image S (fun x => x.2.val - x.1.val) hS_nonempty
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hmem
    obtain ⟨ha'', hb'', hab'', hno''⟩ := hmem
    exact ⟨{
      a := a''
      b := b''
      a_fires := ha''
      b_fires := hb''
      a_lt_b := hab''
      no_fire_between := hno''
      is_min_gap := by
        intro a₃ b₃ ha₃ hb₃ hab₃ hno₃
        exact hmin ⟨a₃, b₃⟩ (by
          simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
          exact ⟨ha₃, hb₃, hab₃, hno₃⟩)
    }, trivial⟩
  · obtain ⟨a', b', hab', ha', hb', hno'⟩ :=
      exists_consecutive_firing_pair gc p b a hba hb ha
    let S : Finset (Fin gc.configs.length × Fin gc.configs.length) :=
      (Finset.univ ×ˢ Finset.univ).filter fun ⟨a'', b''⟩ =>
        gc.moverAt a'' = p ∧ gc.moverAt b'' = p ∧ a''.val < b''.val ∧
        (∀ k : Fin gc.configs.length, a''.val < k.val → k.val < b''.val → gc.moverAt k ≠ p)
    have hS_nonempty : S.Nonempty := by
      refine ⟨⟨a', b'⟩, ?_⟩
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      exact ⟨ha', hb', hab', hno'⟩
    obtain ⟨⟨a'', b''⟩, hmem, hmin⟩ :=
      Finset.exists_min_image S (fun x => x.2.val - x.1.val) hS_nonempty
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hmem
    obtain ⟨ha'', hb'', hab'', hno''⟩ := hmem
    exact ⟨{
      a := a''
      b := b''
      a_fires := ha''
      b_fires := hb''
      a_lt_b := hab''
      no_fire_between := hno''
      is_min_gap := by
        intro a₃ b₃ ha₃ hb₃ hab₃ hno₃
        exact hmin ⟨a₃, b₃⟩ (by
          simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
          exact ⟨ha₃, hb₃, hab₃, hno₃⟩)
    }, trivial⟩

/-- Data-level MinFiringGap from fireCount >= 2 (via Classical.choice). -/
noncomputable def exists_minFiringGap (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hfc : gc.fireCount p ≥ 2) :
    MinFiringGap gc p :=
  (exists_minFiringGap_prop gc p hfc).choose

/-! ### Prefix fire count value preservation -/

/-- When processor p doesn't fire at any step in [a, b), the prefix fire count
    is unchanged: prefixFireCount p b = prefixFireCount p a.

    This is the VALUE-LEVEL version of parity_preserved_of_noFire_between. -/
theorem prefixFireCount_eq_of_noFire_range
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (a b : Nat) (hab : a ≤ b) (hb : b ≤ gc.configs.length)
    (hno : ∀ k : Fin gc.configs.length, a ≤ k.val → k.val < b → gc.moverAt k ≠ p) :
    gc.prefixFireCount p b = gc.prefixFireCount p a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    have hb_lt : b < gc.configs.length := by omega
    have ih' := ih (by omega) (fun k hk1 hk2 => hno k hk1 (by omega))
    rw [gc.prefixFireCount_succ, gc.fireIndicator_of_lt p hb_lt]
    have hne := hno ⟨b, hb_lt⟩ hab (Nat.lt_succ_self b)
    simp [hne, ih']

/-! ### Ring topology helpers -/

private theorem right_ne_self_ipec (i : Fin sys.rs.n) : right i ≠ i := by
  intro h; have hval := congrArg Fin.val h; simp only [right_val] at hval
  have hi := i.isLt; have hn := sys.rs.n_ge_4
  by_cases hp1 : i.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt hp1] at hval; omega
  · rw [show i.val + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega

private theorem right_right_ne_right (i : Fin sys.rs.n) : right (right i) ≠ right i := by
  intro h; have hval := congrArg Fin.val h; simp only [right_val] at hval
  have hi := i.isLt; have hn := sys.rs.n_ge_4
  by_cases hp1 : i.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt hp1] at hval
    by_cases hp2 : i.val + 1 + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt hp2] at hval; omega
    · rw [show i.val + 1 + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega
  · rw [show i.val + 1 = sys.rs.n from by omega, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega : 1 < sys.rs.n)] at hval; omega

/-! ### Parity facts at ri firing steps -/

/-- When ri fires at step b, prefixFireCount(i, b+1) = prefixFireCount(i, b). -/
theorem prefixFireCount_left_preserved_at_ri_step
    (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (b : Fin gc.configs.length)
    (hb_fires : gc.moverAt b = right i) :
    gc.prefixFireCount i (b.val + 1) = gc.prefixFireCount i b.val := by
  rw [gc.prefixFireCount_succ, gc.fireIndicator_of_lt i b.isLt]
  have hne : gc.moverAt b ≠ i := by rw [hb_fires]; exact right_ne_self_ipec i
  simp [hne]

/-- When ri fires at step b, prefixFireCount(rri, b+1) = prefixFireCount(rri, b). -/
theorem prefixFireCount_right_preserved_at_ri_step
    (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (b : Fin gc.configs.length)
    (hb_fires : gc.moverAt b = right i) :
    gc.prefixFireCount (right (right i)) (b.val + 1) =
    gc.prefixFireCount (right (right i)) b.val := by
  rw [gc.prefixFireCount_succ, gc.fireIndicator_of_lt (right (right i)) b.isLt]
  have hne : gc.moverAt b ≠ right (right i) := by
    rw [hb_fires]; exact (right_right_ne_right i).symm
  simp [hne]

/-- When ri fires at step b: prefixFireCount(ri, b+1) = prefixFireCount(ri, b) + 1. -/
theorem prefixFireCount_self_increments_at_ri_step
    (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (b : Fin gc.configs.length)
    (hb_fires : gc.moverAt b = right i) :
    gc.prefixFireCount (right i) (b.val + 1) = gc.prefixFireCount (right i) b.val + 1 :=
  prefixFireCount_step_eq gc (right i) b.val b.isLt hb_fires

/-! ### Cross-gap S-parity matching -/

/-- If ri fires at b₁ and b₂ with no fires of ri in between,
    then prefixFireCount(ri, b₂+1) = prefixFireCount(ri, b₁) + 2.
    Therefore S-parity at non-mover step b₂+1 matches S-parity at mover step b₁. -/
theorem cross_gap_s_parity_match
    (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (b₁ b₂ : Fin gc.configs.length)
    (hb₁ : gc.moverAt b₁ = right i)
    (hb₂ : gc.moverAt b₂ = right i)
    (hlt : b₁.val < b₂.val)
    (hno : ∀ k : Fin gc.configs.length,
      b₁.val < k.val → k.val < b₂.val → gc.moverAt k ≠ right i)
    (hb₂_lt : b₂.val < gc.configs.length) :
    gc.prefixFireCount (right i) (b₂.val + 1) % 2 =
    gc.prefixFireCount (right i) b₁.val % 2 := by
  have h1 := prefixFireCount_self_increments_at_ri_step gc i b₁ hb₁
  have h2 : gc.prefixFireCount (right i) b₂.val =
      gc.prefixFireCount (right i) (b₁.val + 1) :=
    (prefixFireCount_eq_of_noFire_range gc (right i) (b₁.val + 1) b₂.val
      (by omega) (by omega)
      (fun k hk1 hk2 => hno k (by omega) hk2))
  have h3 := prefixFireCount_self_increments_at_ri_step gc i b₂ hb₂
  -- pfc(b₂+1) = pfc(b₂) + 1 = pfc(b₁+1) + 1 = pfc(b₁) + 2
  omega

/-- L-parity at non-mover steps b₁+1 and b₂+1 (after ri fires) can be compared
    via L-parity at the mover steps themselves. -/
theorem cross_gap_l_parity_at_nonmover
    (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (b₁ b₂ : Fin gc.configs.length)
    (hb₁ : gc.moverAt b₁ = right i)
    (hb₂ : gc.moverAt b₂ = right i) :
    gc.prefixFireCount i (b₂.val + 1) % 2 =
    gc.prefixFireCount i (b₁.val + 1) % 2 ↔
    gc.prefixFireCount i b₂.val % 2 =
    gc.prefixFireCount i b₁.val % 2 := by
  rw [prefixFireCount_left_preserved_at_ri_step gc i b₁ hb₁,
      prefixFireCount_left_preserved_at_ri_step gc i b₂ hb₂]

/-- R-parity at non-mover steps can be compared similarly. -/
theorem cross_gap_r_parity_at_nonmover
    (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (b₁ b₂ : Fin gc.configs.length)
    (hb₁ : gc.moverAt b₁ = right i)
    (hb₂ : gc.moverAt b₂ = right i) :
    gc.prefixFireCount (right (right i)) (b₂.val + 1) % 2 =
    gc.prefixFireCount (right (right i)) (b₁.val + 1) % 2 ↔
    gc.prefixFireCount (right (right i)) b₂.val % 2 =
    gc.prefixFireCount (right (right i)) b₁.val % 2 := by
  rw [prefixFireCount_right_preserved_at_ri_step gc i b₁ hb₁,
      prefixFireCount_right_preserved_at_ri_step gc i b₂ hb₂]

/-! ### Cross-gap entry conflict -/

/-- Entry conflict from cross-gap matching: if ri fires at b₁ and b₂ with no
    ri-fires between, and at non-mover step b₂+1 the L, S, R parities match
    mover step b₁, then hasEntryConflict. -/
theorem cross_gap_ec
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (b₁ b₂ : Fin gc.configs.length)
    (hb₁ : gc.moverAt b₁ = right i)
    (hb₂ : gc.moverAt b₂ = right i)
    (hlt : b₁.val < b₂.val)
    (hno : ∀ k : Fin gc.configs.length,
      b₁.val < k.val → k.val < b₂.val → gc.moverAt k ≠ right i)
    (hb₂1 : b₂.val + 1 < gc.configs.length)
    (hb₂1_ne : gc.moverAt ⟨b₂.val + 1, hb₂1⟩ ≠ right i)
    (hL : gc.prefixFireCount i (b₂.val + 1) % 2 =
          gc.prefixFireCount i b₁.val % 2)
    (hR : gc.prefixFireCount (right (right i)) (b₂.val + 1) % 2 =
          gc.prefixFireCount (right (right i)) b₁.val % 2) :
    hasEntryConflict gc := by
  have hS := cross_gap_s_parity_match gc i b₁ b₂ hb₁ hb₂ hlt hno b₂.isLt
  exact cross_gap_parity_ec h3bin b₁ ⟨b₂.val + 1, hb₂1⟩ hb₁ hb₂1_ne hL hS hR

/-! ### MinFiringGap gap >= 2 from isolation -/

/-- When all firings of p are isolated and fireCount >= 2, the MinFiringGap
    has gap >= 2. -/
theorem isolated_minFiringGap_gap_ge2
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hfc : gc.fireCount p ≥ 2)
    (hiso : ∀ (a : Fin gc.configs.length),
      gc.moverAt a = p → gc.moverAt (nextIndex gc.configs a) ≠ p) :
    (exists_minFiringGap gc p hfc).b.val - (exists_minFiringGap gc p hfc).a.val ≥ 2 :=
  allIsolated_gap_ge2 (exists_minFiringGap gc p hfc) hiso

/-! ### MinFiringGap entry conflict with parity conditions -/

/-- For 3 consecutive binary {i, ri, rri}, the MinFiringGap for ri gives entry
    conflict when both neighbors' prefix fire counts have matching parities. -/
theorem isolated_minGap_ec_of_parity_match
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (hfc : gc.fireCount (right i) ≥ 2)
    (hiso : ∀ (a : Fin gc.configs.length),
      gc.moverAt a = right i → gc.moverAt (nextIndex gc.configs a) ≠ right i)
    (hL_par : let mg := exists_minFiringGap gc (right i) hfc
              gc.prefixFireCount i (mg.a.val + 1) % 2 =
              gc.prefixFireCount i mg.b.val % 2)
    (hR_par : let mg := exists_minFiringGap gc (right i) hfc
              gc.prefixFireCount (right (right i)) (mg.a.val + 1) % 2 =
              gc.prefixFireCount (right (right i)) mg.b.val % 2) :
    hasEntryConflict gc :=
  minGap_parity_ec h3bin (exists_minFiringGap gc (right i) hfc)
    (allIsolated_gap_ge2 _ hiso) hL_par hR_par

end LeanMn
