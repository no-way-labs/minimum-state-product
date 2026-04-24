/-
  ParityWalk.lean — Entry conflict via parity walk for 3 consecutive binary

  For 3 consecutive binary processors {i, p, q} where p = right i, q = right p:
  since all three are binary, the context (L, S, R) at p is determined by
  prefix-fire-count parities.

  Main theorems (all sorry-free):

  1. `general_parity_entry_conflict`: entry conflict from matching parity triples
     at ANY mover/non-mover step pair (generalizes procMinGap_hasEntryConflict).

  2. `parity_preserved_of_noFire_between`: S-parity preservation when p doesn't
     fire between two steps.

  3. `prefixFireCount_step_eq` / `prefixFireCount_step_ne`: step-by-step
     decomposition of prefix fire counts for parity tracking.

  4. `prefixFireCount_parity_flip` / `prefixFireCount_parity_same`: parity
     changes when a processor fires or doesn't fire.

  5. `allIsolated_gap_ge2`: the min gap is ≥ 2 when all firings are isolated.

  6. `cross_gap_parity_ec`: entry conflict from cross-gap parity matching
     (mover step in one gap matched with non-mover step in another).

  7. `not_permanent_of_other_fires`: eliminates the "permanent mover" case
     when another processor is known to fire.
-/
import LeanMn.LowerBound.EntryConflict.ProcMinGap
import LeanMn.LowerBound.EntryConflict.IsolatedFirings

namespace LeanMn

variable {sys : System}

/-! ### Generalized entry conflict from parity triples -/

/-- Entry conflict at processor `right i` between steps t (non-mover) and b
    (mover), when all three binary processors' prefix fire count parities match.

    This generalizes `procMinGap_hasEntryConflict` to work with ANY non-mover
    step t, not just step a+1 of a MinFiringGap. The non-mover step t and
    mover step b can be in different gaps or even far apart in the cycle. -/
theorem general_parity_entry_conflict
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (t : Nat) (ht : t < gc.configs.length)
    (b : Nat) (hb : b < gc.configs.length)
    (hb_fires : gc.moverAt ⟨b, hb⟩ = right i)
    (ht_ne : gc.moverAt ⟨t, ht⟩ ≠ right i)
    (hL_par : gc.prefixFireCount i t % 2 = gc.prefixFireCount i b % 2)
    (hS_par : gc.prefixFireCount (right i) t % 2 =
              gc.prefixFireCount (right i) b % 2)
    (hR_par : gc.prefixFireCount (right (right i)) t % 2 =
              gc.prefixFireCount (right (right i)) b % 2) :
    hasEntryConflict gc := by
  have hL := binary_config_eq_of_prefix_parity gc i h3bin.1 ht hb hL_par
  have hS := binary_config_eq_of_prefix_parity gc (right i) h3bin.2.1 ht hb hS_par
  have hR := binary_config_eq_of_prefix_parity gc (right (right i)) h3bin.2.2 ht hb hR_par
  exact ⟨⟨b, hb⟩, ⟨t, ht⟩, right i, hb_fires, ht_ne,
    by rw [left_right_eq_self]; exact hL.symm,
    hS.symm, hR.symm⟩

/-! ### S-parity preservation -/

/-- When processor p doesn't fire between steps t and b (no step in [t, b) has
    moverAt = p), the prefix fire count parity of p is preserved. -/
theorem parity_preserved_of_noFire_between
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (t b : Nat) (htb : t ≤ b) (hb : b ≤ gc.configs.length)
    (hno : ∀ k : Fin gc.configs.length, t ≤ k.val → k.val < b → gc.moverAt k ≠ p) :
    gc.prefixFireCount p t % 2 = gc.prefixFireCount p b % 2 := by
  induction b, htb using Nat.le_induction with
  | base => rfl
  | succ b htb ih =>
    have hb_lt : b < gc.configs.length := by omega
    have ih' := ih (by omega) (fun k hk1 hk2 => hno k hk1 (by omega))
    rw [gc.prefixFireCount_succ, gc.fireIndicator_of_lt p hb_lt]
    have hne := hno ⟨b, hb_lt⟩ htb (Nat.lt_succ_self b)
    simp [hne]; omega

/-! ### Prefix fire count step decomposition -/

/-- The prefix fire count at m+1 = count at m + 1 when p fires at m. -/
theorem prefixFireCount_step_eq (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (m : Nat) (hm : m < gc.configs.length)
    (hmov : gc.moverAt ⟨m, hm⟩ = p) :
    gc.prefixFireCount p (m + 1) = gc.prefixFireCount p m + 1 := by
  rw [gc.prefixFireCount_succ, gc.fireIndicator_of_lt p hm, hmov]; simp

/-- The prefix fire count at m+1 = count at m when p doesn't fire at m. -/
theorem prefixFireCount_step_ne (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (m : Nat) (hm : m < gc.configs.length)
    (hmov : gc.moverAt ⟨m, hm⟩ ≠ p) :
    gc.prefixFireCount p (m + 1) = gc.prefixFireCount p m := by
  rw [gc.prefixFireCount_succ, gc.fireIndicator_of_lt p hm]
  simp [hmov]

/-- Parity flips when p fires. -/
theorem prefixFireCount_parity_flip (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (m : Nat) (hm : m < gc.configs.length)
    (hmov : gc.moverAt ⟨m, hm⟩ = p) :
    gc.prefixFireCount p (m + 1) % 2 = (gc.prefixFireCount p m + 1) % 2 := by
  rw [prefixFireCount_step_eq gc p m hm hmov]

/-- Parity stays when p doesn't fire. -/
theorem prefixFireCount_parity_same (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (m : Nat) (hm : m < gc.configs.length)
    (hmov : gc.moverAt ⟨m, hm⟩ ≠ p) :
    gc.prefixFireCount p (m + 1) % 2 = gc.prefixFireCount p m % 2 := by
  rw [prefixFireCount_step_ne gc p m hm hmov]

/-! ### Gap ≥ 2 from all-isolated -/

/-- When all firings of p are isolated (no consecutive fires), any MinFiringGap
    has gap ≥ 2. -/
theorem allIsolated_gap_ge2
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p)
    (hiso : ∀ (a : Fin gc.configs.length),
      gc.moverAt a = p → gc.moverAt (nextIndex gc.configs a) ≠ p) :
    mg.b.val - mg.a.val ≥ 2 := by
  by_contra hlt; push_neg at hlt
  have hgap1 : mg.b.val = mg.a.val + 1 := by
    have := mg.a_lt_b; omega
  have ha1_lt : mg.a.val + 1 < gc.configs.length := by
    have := mg.b.isLt; omega
  have hnext_eq : nextIndex gc.configs mg.a = ⟨mg.a.val + 1, ha1_lt⟩ :=
    Fin.ext (by simp [nextIndex, Nat.mod_eq_of_lt ha1_lt])
  have hb_eq : mg.b = ⟨mg.a.val + 1, ha1_lt⟩ := Fin.ext hgap1
  exact hiso mg.a mg.a_fires (by rw [hnext_eq, ← hb_eq]; exact mg.b_fires)

/-! ### Cross-gap entry conflict -/

/-- Entry conflict between a mover step s₁ of p = right i and a non-mover step
    s₂ of p, where the parity triples match. Wrapper around
    `general_parity_entry_conflict` with `Fin`-indexed steps. -/
theorem cross_gap_parity_ec
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (s₁ : Fin gc.configs.length)
    (s₂ : Fin gc.configs.length)
    (hs₁ : gc.moverAt s₁ = right i)
    (hs₂ : gc.moverAt s₂ ≠ right i)
    (hL : gc.prefixFireCount i s₂.val % 2 = gc.prefixFireCount i s₁.val % 2)
    (hS : gc.prefixFireCount (right i) s₂.val % 2 =
          gc.prefixFireCount (right i) s₁.val % 2)
    (hR : gc.prefixFireCount (right (right i)) s₂.val % 2 =
          gc.prefixFireCount (right (right i)) s₁.val % 2) :
    hasEntryConflict gc :=
  general_parity_entry_conflict h3bin s₂.val s₂.isLt s₁.val s₁.isLt hs₁ hs₂ hL hS hR

/-! ### Permanent mover elimination -/

/-- If p fires at every step but some step has mover = q ≠ p, contradiction. -/
theorem not_permanent_of_other_fires
    (gc : GoodCycle sys) (r : Fin sys.rs.n)
    (q : Fin sys.rs.n) (hne : q ≠ r)
    (k : Fin gc.configs.length) (hmov : gc.moverAt k = q) :
    ¬(∀ j : Fin gc.configs.length, gc.moverAt j = r) := by
  intro hperm
  exact hne (hmov ▸ hperm k)

/-! ### Entry conflict from MinFiringGap with parity conditions -/

/-- Wrapper: given a MinFiringGap for `right i` in the 3-consecutive-binary
    setting, if the L and R parity conditions hold for the gap, derive entry
    conflict. The S-parity condition is automatic (p doesn't fire in the gap).

    This is a more explicit version of `procMinGap_hasEntryConflict` that
    makes the S-parity argument visible. -/
theorem minGap_parity_ec
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (mg : MinFiringGap gc (right i))
    (hgap2 : mg.b.val - mg.a.val ≥ 2)
    (hL_par : gc.prefixFireCount i (mg.a.val + 1) % 2 =
              gc.prefixFireCount i mg.b.val % 2)
    (hR_par : gc.prefixFireCount (right (right i)) (mg.a.val + 1) % 2 =
              gc.prefixFireCount (right (right i)) mg.b.val % 2) :
    hasEntryConflict gc := by
  have ha1_lt : mg.a.val + 1 < gc.configs.length := by
    have := mg.b.isLt; omega
  -- S-parity: right i doesn't fire in (a, b), so prefix fire count of right i
  -- at a+1 and b have the same parity.
  have hS_par : gc.prefixFireCount (right i) (mg.a.val + 1) % 2 =
                gc.prefixFireCount (right i) mg.b.val % 2 := by
    apply parity_preserved_of_noFire_between gc (right i) (mg.a.val + 1) mg.b.val
    · omega
    · exact Nat.le_of_lt mg.b.isLt
    · intro k hk1 hk2
      exact mg.no_fire_between k (by omega) hk2
  -- Non-mover step a+1 (right i doesn't fire there)
  have ha_lt_a1 : mg.a.val < mg.a.val + 1 := Nat.lt_succ_self _
  have ha1_lt_b : mg.a.val + 1 < mg.b.val := by omega
  have ht_ne : gc.moverAt ⟨mg.a.val + 1, ha1_lt⟩ ≠ right i :=
    mg.no_fire_between ⟨mg.a.val + 1, ha1_lt⟩ ha_lt_a1 ha1_lt_b
  exact general_parity_entry_conflict h3bin (mg.a.val + 1) ha1_lt mg.b.val mg.b.isLt
    mg.b_fires ht_ne hL_par hS_par hR_par

end LeanMn
