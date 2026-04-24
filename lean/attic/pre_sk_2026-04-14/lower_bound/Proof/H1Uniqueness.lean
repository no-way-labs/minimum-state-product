/-
  H1Uniqueness.lean — Hamming-1 uniqueness for good cycles

  Lemma: In a good cycle with m_i ∈ {2,3}, fc(i) = m_i for all i,
  and gcd(m_0, ..., m_{n-1}) = 1: if g_j and g_k differ at exactly one
  position p, then j and k are adjacent in the cycle.

  Proof (from lb_complete_proof.md, "The H-1 Uniqueness Lemma"):
  1. Value Coverage: fc(p) = m_p → visits all m_p values exactly once
  2. Arc Return: Hamming-1 pair at p with arc distance d →
     fire count in arc is 0 or m_q for each q ≠ p
  3. GCD Obstruction: periodicity d | CL contradicts gcd = 1

  Used by ShadowOrbit for the sweep non-consecutive case.

  Sorry map:
  - `value_coverage_ternary` — ternary proc visits all 3 values
    Maps to: lb_complete_proof.md §"Lemma 1 (Value Coverage)"
  - `arc_return` — fire count in arc is 0 or m_q
    Maps to: lb_complete_proof.md §"Lemma 2 (Arc Return)"
  - `gcd_obstruction` — periodicity contradicts gcd = 1
    Maps to: lb_complete_proof.md §"Lemma 3 (GCD Obstruction)"
  - `h1_uniqueness` — main result
    Maps to: lb_complete_proof.md §"The H-1 Uniqueness Lemma"
-/
import LeanMn.LowerBound.EntryConflict.BinaryParity
import LeanMn.LowerBound.EntryConflict.PhaseExtractionBase

namespace LeanMn

variable {sys : System}

/-! ### Hamming distance -/

/-- Two configs differ at exactly one position. -/
def hammingOne (rs : RingSpec) (c₁ c₂ : Config rs) : Prop :=
  ∃ p : Fin rs.n, c₁ p ≠ c₂ p ∧ ∀ q : Fin rs.n, q ≠ p → c₁ q = c₂ q

/-! ### Value Coverage -/

/-- Value Coverage: binary proc with fc = 2 visits both values. -/
theorem value_coverage_binary
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hm : sys.rs.m p = 2) (hfc : gc.fireCount p = 2) :
    ∀ v : Fin (sys.rs.m p), ∃ j : Fin gc.configs.length,
      (gc.configs.get j) p = v := by
  -- Extract a firing step from fc ≥ 1
  have ⟨k, hk_mov⟩ : ∃ k : Fin gc.configs.length, gc.moverAt k = p := by
    by_contra hall; push_neg at hall
    have : gc.fireCount p = 0 := by
      rw [gc.fireCount_eq_sum_moverAt]; apply Finset.sum_eq_zero
      intro j _; simp [hall j]
    omega
  -- Value changes at step k
  have hne := gc.state_ne_at_moverAt k
  rw [hk_mov] at hne
  -- Two distinct values in Fin (sys.rs.m p)
  set v₀ := (gc.configs.get k) p
  set v₁ := (gc.configs.get (nextIndex gc.configs k)) p
  have hv0_lt : v₀.val < 2 := hm ▸ v₀.isLt
  have hv1_lt : v₁.val < 2 := hm ▸ v₁.isLt
  have hne_val : v₀.val ≠ v₁.val := fun h => hne (Fin.ext h).symm
  -- For any target v: Fin 2 exhaustion
  intro v
  have hv_lt : v.val < 2 := hm ▸ v.isLt
  by_cases hv0 : v = v₀
  · exact ⟨k, hv0.symm⟩
  · have hv_ne : v.val ≠ v₀.val := fun h => hv0 (Fin.ext h)
    exact ⟨nextIndex gc.configs k, Fin.ext (by omega)⟩

/-- Value Coverage: ternary proc with fc = 3 visits all 3 values.
    Proof by contradiction: if some value is missed, the walk is confined
    to 2 values. A closed walk on 2 values with 3 changes (odd) cannot
    return to start.

    SORRY: The parity induction needs `stateAfter_succ_eq_next` which is
    private in GoodCycleBasics. Needs either exposing that lemma or
    reproving it locally. The mathematical argument is:
    1. Assume v_miss never appears → walk on 2 values {v₀, v₁}
    2. Each fire flips between v₀ and v₁ (only 2 options, must change)
    3. prefixFireCount p CL = 3 (odd) → stateAfter CL ≠ stateAfter 0
    4. But cyclic return: stateAfter CL = stateAfter 0. Contradiction.
    Maps to: lb_complete_proof.md §"Lemma 1 (Value Coverage)" -/
theorem value_coverage_ternary
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hm : sys.rs.m p = 3) (hfc : gc.fireCount p = 3) :
    ∀ v : Fin (sys.rs.m p), ∃ j : Fin gc.configs.length,
      (gc.configs.get j) p = v := by
  by_contra hnocover
  push_neg at hnocover
  obtain ⟨v_miss, hv_miss⟩ := hnocover
  -- Extract a firing step for two distinct visited values
  have ⟨k, hk⟩ : ∃ k : Fin gc.configs.length, gc.moverAt k = p := by
    by_contra hall; push_neg at hall
    have : gc.fireCount p = 0 := by
      rw [gc.fireCount_eq_sum_moverAt]; apply Finset.sum_eq_zero
      intro j _; simp [hall j]
    omega
  set v₀ := (gc.configs.get ⟨0, gc.configs_length_pos⟩) p with hv₀_def
  have hv₀_ne : v₀ ≠ v_miss := hv_miss ⟨0, gc.configs_length_pos⟩
  -- Parity induction: stateAfter p j = v₀ ↔ Even (prefixFireCount p j)
  -- Under the constraint that only 2 values appear (v₀ and one other),
  -- each fire toggles and each non-fire preserves.
  have hparity : ∀ j : Nat, j ≤ gc.configs.length →
      (gc.stateAfter p j = v₀ ↔ Even (gc.prefixFireCount p j)) := by
    intro j hj
    induction j with
    | zero =>
      simp [GoodCycle.stateAfter_of_lt gc p gc.configs_length_pos, hv₀_def]
    | succ j ih =>
      by_cases hjlt : j < gc.configs.length
      · have ih' := ih (by omega)
        rw [GoodCycle.prefixFireCount_succ]
        by_cases hfire : gc.moverAt ⟨j, hjlt⟩ = p
        · -- Fire: value flips, indicator = 1, parity flips
          have hind : gc.fireIndicator p j = 1 := by
            simp [GoodCycle.fireIndicator, hjlt, hfire]
          rw [hind]
          -- stateAfter(j+1) ≠ stateAfter(j)
          have hsa_j : gc.stateAfter p j = (gc.configs.get ⟨j, hjlt⟩) p :=
            gc.stateAfter_of_lt p hjlt
          have hsa_j1 : gc.stateAfter p (j + 1) =
              (gc.configs.get (nextIndex gc.configs ⟨j, hjlt⟩)) p :=
            gc.stateAfter_succ_eq_next p hjlt
          have hflip : gc.stateAfter p (j + 1) ≠ gc.stateAfter p j := by
            rw [hsa_j, hsa_j1]
            have := gc.state_ne_at_moverAt ⟨j, hjlt⟩
            rwa [hfire] at this
          -- Both values ≠ v_miss, so in a 2-element set in Fin 3
          have hne_j : (gc.stateAfter p j).val ≠ v_miss.val := by
            rw [hsa_j]; intro h; exact hv_miss _ (Fin.ext h)
          have hne_j1 : (gc.stateAfter p (j + 1)).val ≠ v_miss.val := by
            rw [hsa_j1]
            intro h
            have hmem : (gc.configs.get (nextIndex gc.configs ⟨j, hjlt⟩)) p = v_miss :=
              Fin.ext h
            exact hv_miss _ hmem
          have hlt_j : (gc.stateAfter p j).val < 3 := hm ▸ (gc.stateAfter p j).isLt
          have hlt_j1 : (gc.stateAfter p (j + 1)).val < 3 := hm ▸ (gc.stateAfter p (j + 1)).isLt
          have hlt_v0 : v₀.val < 3 := hm ▸ v₀.isLt
          have hlt_miss : v_miss.val < 3 := hm ▸ v_miss.isLt
          have hne_v0_miss : v₀.val ≠ v_miss.val := fun h => hv₀_ne (Fin.ext h)
          have hne_flip_val : (gc.stateAfter p j).val ≠ (gc.stateAfter p (j + 1)).val :=
            fun h => hflip (Fin.ext h).symm
          -- Key equivalence via omega on Fin.val:
          -- In {0,1,2} \ {v_miss.val}: stateAfter(j+1) = v₀ ↔ stateAfter(j) ≠ v₀
          have hswap : (gc.stateAfter p (j + 1)).val = v₀.val ↔
              (gc.stateAfter p j).val ≠ v₀.val := by
            constructor
            · intro h1 h2; exact hne_flip_val (by omega)
            · intro h; omega
          constructor
          · -- →: stateAfter(j+1) = v₀ → Even(prefix + 1)
            intro heq
            have hne_j : (gc.stateAfter p j).val ≠ v₀.val :=
              hswap.mp (congrArg Fin.val heq)
            have hodd : ¬Even (gc.prefixFireCount p j) :=
              fun hev => hne_j (congrArg Fin.val (ih'.mpr hev))
            rwa [Nat.even_add_one]
          · -- ←: Even(prefix + 1) → stateAfter(j+1) = v₀
            intro heven
            rw [Nat.even_add_one] at heven
            have hodd : ¬Even (gc.prefixFireCount p j) := heven
            have hne_j : gc.stateAfter p j ≠ v₀ := fun h => hodd (ih'.mp h)
            have hne_j_val : (gc.stateAfter p j).val ≠ v₀.val :=
              fun h => hne_j (Fin.ext h)
            exact Fin.ext (hswap.mpr hne_j_val)
        · -- No fire: value unchanged, indicator = 0
          have hind : gc.fireIndicator p j = 0 := by
            simp [GoodCycle.fireIndicator, hjlt,
              show gc.moverAt ⟨j, hjlt⟩ ≠ p from hfire]
          rw [hind, Nat.add_zero]
          have hsame : gc.stateAfter p (j + 1) = gc.stateAfter p j := by
            have hsa_j : gc.stateAfter p j = (gc.configs.get ⟨j, hjlt⟩) p :=
              gc.stateAfter_of_lt p hjlt
            have hsa_j1 : gc.stateAfter p (j + 1) =
                (gc.configs.get (nextIndex gc.configs ⟨j, hjlt⟩)) p :=
              gc.stateAfter_succ_eq_next p hjlt
            rw [hsa_j, hsa_j1]
            exact gc.state_eq_of_ne_moverAt ⟨j, hjlt⟩ p (Ne.symm hfire)
          rw [hsame]; exact ih'
      · -- j ≥ CL but j+1 ≤ CL → contradiction (CL ≥ 1)
        omega
  -- Apply at CL: stateAfter CL = v₀ (wraps) but prefixFireCount = 3 (odd)
  have hstart : gc.stateAfter p gc.configs.length = v₀ := by
    -- stateAfter_of_ge gives stateAfter CL = configs.get firstIndex p
    -- firstIndex = ⟨0, _⟩, same as our definition of v₀
    simp only [GoodCycle.stateAfter, show ¬(gc.configs.length < gc.configs.length) from by omega]
    rfl
  have heven3 := (hparity gc.configs.length le_rfl).mp hstart
  rw [show gc.prefixFireCount p gc.configs.length = gc.fireCount p from rfl, hfc] at heven3
  exact (Nat.not_even_iff_odd.mpr (by decide)) heven3

/-! ### stateAfter wrap helpers -/

/-- stateAfter CL = configs.get 0 (cyclic wrap). -/
private theorem stateAfter_length_eq_config0 (gc : GoodCycle sys) (q : Fin sys.rs.n) :
    gc.stateAfter q gc.configs.length = (gc.configs.get ⟨0, gc.configs_length_pos⟩) q := by
  simp only [GoodCycle.stateAfter, show ¬(gc.configs.length < gc.configs.length) from by omega]
  rfl

/-- If ifc(a, CL) = 1, then stateAfter CL ≠ stateAfter a.
    Same induction as value_ne_of_single_fire but for the wrap boundary.
    SORRY: mechanical — same pattern as value_ne_of_single_fire but with
    stateAfter instead of configs.get. Needs s+1 < CL derivation from
    ifc(s+1,CL) = 1. -/
private theorem stateAfter_ne_of_single_fire_to_end
    (gc : GoodCycle sys) (q : Fin sys.rs.n)
    (a : Nat) (ha : a < gc.configs.length)
    (hifc : gc.intervalFireCount q a gc.configs.length = 1) :
    gc.stateAfter q gc.configs.length ≠ gc.stateAfter q a := by
  -- Induction on (CL - a)
  suffices ∀ d (s : Nat), s < gc.configs.length → gc.configs.length - s = d →
      gc.intervalFireCount q s gc.configs.length = 1 →
      gc.stateAfter q gc.configs.length ≠ gc.stateAfter q s by
    exact this _ a ha rfl hifc
  intro d; induction d with
  | zero => intro s hs hd; omega
  | succ d ih =>
    intro s hs hd hifc_s
    -- Split: ifc(s, CL) = ifc(s, s+1) + ifc(s+1, CL)
    have hs1_le : s + 1 ≤ gc.configs.length := by omega
    have hspl := intervalFireCount_split gc q (show s ≤ s + 1 by omega) hs1_le
    by_cases hf : gc.moverAt ⟨s, hs⟩ = q
    · -- Fire at s. ifc(s,s+1) = 1, ifc(s+1,CL) = 0.
      have h1 : gc.intervalFireCount q s (s + 1) = 1 := by
        simp only [GoodCycle.intervalFireCount, GoodCycle.prefixFireCount,
          Finset.sum_range_succ, Finset.sum_range_zero]
        simp [GoodCycle.fireIndicator, hs, hf]
      have h0 : gc.intervalFireCount q (s + 1) gc.configs.length = 0 := by omega
      -- stateAfter CL = stateAfter(s+1) (no fires in [s+1,CL))
      have hchain := gc.stateAfter_eq_of_no_fire q hs1_le le_rfl
        (fun t ht1 ht2 hm => by
          have := intervalFireCount_split gc q (show s + 1 ≤ t.val from ht1)
            (show t.val ≤ gc.configs.length from Nat.le_of_lt t.isLt)
          have := intervalFireCount_split gc q (show t.val ≤ t.val + 1 by omega)
            (show t.val + 1 ≤ gc.configs.length by omega)
          have : gc.intervalFireCount q t.val (t.val + 1) ≥ 1 := by
            simp only [GoodCycle.intervalFireCount, GoodCycle.prefixFireCount,
              Finset.sum_range_succ, Finset.sum_range_zero]
            simp [GoodCycle.fireIndicator, t.isLt, hm]
          omega)
      -- stateAfter(s+1) ≠ stateAfter(s) (fire at s)
      have hne : gc.stateAfter q (s + 1) ≠ gc.stateAfter q s := by
        rw [gc.stateAfter_succ_eq_next q hs, gc.stateAfter_of_lt q hs]
        have := gc.state_ne_at_moverAt ⟨s, hs⟩; rwa [hf] at this
      -- Compose: stateAfter CL = stateAfter(s+1) ≠ stateAfter(s)
      intro heq; exact hne (hchain.symm.trans heq)
    · -- No fire at s. ifc(s,s+1) = 0, ifc(s+1,CL) = 1.
      have h0 : gc.intervalFireCount q s (s + 1) = 0 := by
        simp only [GoodCycle.intervalFireCount, GoodCycle.prefixFireCount,
          Finset.sum_range_succ, Finset.sum_range_zero]
        simp [GoodCycle.fireIndicator, hs, hf]
      have h1 : gc.intervalFireCount q (s + 1) gc.configs.length = 1 := by omega
      -- s+1 < CL (from ifc(s+1,CL) = 1 ≥ 1, so s+1 ≠ CL)
      have hs1_lt : s + 1 < gc.configs.length := by
        by_contra hge; push_neg at hge
        have : s + 1 = gc.configs.length := by omega
        have : gc.intervalFireCount q (s + 1) gc.configs.length = 0 := by
          rw [this]; simp [GoodCycle.intervalFireCount]
        omega
      -- stateAfter(s+1) = stateAfter(s) (no fire at s)
      have hsame : gc.stateAfter q (s + 1) = gc.stateAfter q s := by
        rw [gc.stateAfter_succ_eq_next q hs,
            gc.state_eq_of_ne_moverAt ⟨s, hs⟩ q (Ne.symm hf),
            ← gc.stateAfter_of_lt q hs]
      -- IH: stateAfter CL ≠ stateAfter(s+1)
      have hih := ih (s + 1) hs1_lt (by omega) h1
      -- Compose: stateAfter CL ≠ stateAfter(s+1) = stateAfter(s)
      intro heq; exact hih (heq.trans hsame.symm)

/-- Sum of all interval fire counts = interval length. Each step has one mover.
    Proof: same as sum_fireCount but for sub-intervals. Swap sums, apply
    sum_fireIndicator_eq_one at each step. -/
private theorem sum_prefixFireCount_eq
    (gc : GoodCycle sys) (m : Nat) (hm : m ≤ gc.configs.length) :
    ∑ q : Fin sys.rs.n, gc.prefixFireCount q m = m := by
  classical
  unfold GoodCycle.prefixFireCount
  rw [Finset.sum_comm]
  calc ∑ k ∈ Finset.range m, ∑ q : Fin sys.rs.n, gc.fireIndicator q k
      = ∑ _k ∈ Finset.range m, 1 := by
        apply Finset.sum_congr rfl; intro k hk
        exact gc.sum_fireIndicator_eq_one (Nat.lt_of_lt_of_le (Finset.mem_range.mp hk) hm)
    _ = m := by simp

private theorem sum_intervalFireCount_eq
    (gc : GoodCycle sys) (a b : Nat) (hab : a ≤ b) (hb : b ≤ gc.configs.length) :
    ∑ q : Fin sys.rs.n, gc.intervalFireCount q a b = b - a := by
  -- ifc(q,a,b) = pfc(q,b) - pfc(q,a). Sum = Σ pfc(b) - Σ pfc(a) = b - a.
  -- Nat subtraction: need pfc(q,b) ≥ pfc(q,a) for each q.
  have hmono : ∀ q : Fin sys.rs.n, gc.prefixFireCount q a ≤ gc.prefixFireCount q b := by
    intro q; unfold GoodCycle.prefixFireCount
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hab)
  have hsum_b := sum_prefixFireCount_eq gc b hb
  have hsum_a := sum_prefixFireCount_eq gc a (by omega)
  -- Σ (pfc(b) - pfc(a)) = Σ pfc(b) - Σ pfc(a) when each term is non-negative
  have : ∑ q : Fin sys.rs.n, gc.intervalFireCount q a b =
      (∑ q : Fin sys.rs.n, gc.prefixFireCount q b) -
        (∑ q : Fin sys.rs.n, gc.prefixFireCount q a) := by
    simp only [GoodCycle.intervalFireCount]
    -- Σ (f - g) + Σ g = Σ f when g ≤ f pointwise
    suffices h : ∑ q : Fin sys.rs.n, (gc.prefixFireCount q b - gc.prefixFireCount q a) +
        ∑ q : Fin sys.rs.n, gc.prefixFireCount q a =
        ∑ q : Fin sys.rs.n, gc.prefixFireCount q b by
      have hle_sum : ∑ q : Fin sys.rs.n, gc.prefixFireCount q a ≤
          ∑ q : Fin sys.rs.n, gc.prefixFireCount q b :=
        Finset.sum_le_sum (fun q _ => hmono q)
      omega
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro q _
    have := hmono q; omega
  rw [this, hsum_b, hsum_a]

/-! ### Arc Return -/

/-- If q fires exactly once in [a,b) with a < b ≤ CL, config values at a
    and b differ at q. Proof: find the unique fire step s. Value is constant
    [a,s) and [s+1,b). Fire at s changes value. Compose. -/
private theorem value_ne_of_single_fire
    (gc : GoodCycle sys) (q : Fin sys.rs.n)
    (a b : Nat) (hab : a < b) (hb : b < gc.configs.length)
    (hifc : gc.intervalFireCount q a b = 1) :
    (gc.configs.get ⟨a, by omega⟩) q ≠ (gc.configs.get ⟨b, hb⟩) q := by
  -- Induction on (b - a). At each step: if q fires at a, value changes and
  -- rest has 0 fires (constant). If not, value preserved, recurse on [a+1,b).
  suffices hsuff : ∀ d (a : Nat) (ha : a < b),
      b - a = d →
      gc.intervalFireCount q a b = 1 →
      (gc.configs.get ⟨a, Nat.lt_trans ha hb⟩) q ≠ (gc.configs.get ⟨b, hb⟩) q from
    hsuff (b - a) a hab rfl hifc
  intro d
  induction d with
  | zero => intro a _ hd; omega
  | succ d ih =>
    intro a hd hab' hifc'
    have ha_lt : a < gc.configs.length := by omega
    -- Split: ifc(a,b) = ifc(a,a+1) + ifc(a+1,b)
    have hsplit := intervalFireCount_split gc q
      (show a ≤ a + 1 by omega) (show a + 1 ≤ b by omega)
    by_cases hfire : gc.moverAt ⟨a, ha_lt⟩ = q
    · -- Fire at a: ifc(a,a+1) = 1, so ifc(a+1,b) = 0
      have hifc_a : gc.intervalFireCount q a (a + 1) = 1 := by
        simp only [GoodCycle.intervalFireCount, GoodCycle.prefixFireCount,
          Finset.sum_range_succ, Finset.sum_range_zero]
        simp [GoodCycle.fireIndicator, ha_lt, hfire]
      have hifc_rest : gc.intervalFireCount q (a + 1) b = 0 := by omega
      -- val(a+1) = val(b) (no fires in [a+1,b))
      have hval_rest := configVal_eq_of_noFire_between gc q (a + 1) b
        (by omega) hb (fun k hk1 hk2 hmov => by
          have : gc.intervalFireCount q (a + 1) b ≥ 1 := by
            have hs := intervalFireCount_split gc q
              (show a + 1 ≤ k.val by omega) (show k.val ≤ b by omega)
            have hs2 := intervalFireCount_split gc q
              (show k.val ≤ k.val + 1 by omega) (show k.val + 1 ≤ b by omega)
            have : gc.intervalFireCount q k.val (k.val + 1) ≥ 1 := by
              simp only [GoodCycle.intervalFireCount, GoodCycle.prefixFireCount,
                Finset.sum_range_succ, Finset.sum_range_zero]
              simp [GoodCycle.fireIndicator, k.isLt, hmov]
            omega
          omega)
      -- val(a) ≠ val(a+1) (fire at a)
      have hne := gc.state_ne_at_moverAt ⟨a, ha_lt⟩
      rw [hfire] at hne
      have hnext : nextIndex gc.configs ⟨a, ha_lt⟩ = ⟨a + 1, by omega⟩ := by
        ext; simp [nextIndex, Nat.mod_eq_of_lt (by omega : a + 1 < gc.configs.length)]
      rw [hnext] at hne
      -- Compose: val(a) ≠ val(a+1) = val(b)
      intro heq; exact hne (by rw [heq, hval_rest])
    · -- No fire at a: val(a) = val(a+1), ifc(a+1,b) = 1, recurse
      have hifc_a : gc.intervalFireCount q a (a + 1) = 0 := by
        simp only [GoodCycle.intervalFireCount, GoodCycle.prefixFireCount,
          Finset.sum_range_succ, Finset.sum_range_zero]
        simp [GoodCycle.fireIndicator, ha_lt, hfire]
      have hifc_rest : gc.intervalFireCount q (a + 1) b = 1 := by omega
      -- val(a) = val(a+1) (no fire at a)
      have hval_same : (gc.configs.get ⟨a, ha_lt⟩) q =
          (gc.configs.get ⟨a + 1, by omega⟩) q := by
        have hstep := gc.state_eq_of_ne_moverAt ⟨a, ha_lt⟩ q (Ne.symm hfire)
        have hnext : nextIndex gc.configs ⟨a, ha_lt⟩ = ⟨a + 1, by omega⟩ := by
          ext; simp [nextIndex, Nat.mod_eq_of_lt (by omega : a + 1 < gc.configs.length)]
        rw [hnext] at hstep; exact hstep.symm
      -- IH: val(a+1) ≠ val(b)
      have ha1_lt_b : a + 1 < b := by
        by_contra hge; push_neg at hge
        have hab1 : b ≤ a + 1 := hge
        have : gc.intervalFireCount q (a + 1) b = 0 := by
          unfold GoodCycle.intervalFireCount
          have : gc.prefixFireCount q b ≤ gc.prefixFireCount q (a + 1) := by
            unfold GoodCycle.prefixFireCount
            exact Finset.sum_le_sum_of_subset (Finset.range_mono hab1)
          omega
        omega
      have hih := ih (a + 1) ha1_lt_b (by omega) hifc_rest
      -- Compose
      intro heq; exact hih (by rw [← hval_same, heq])

theorem arc_return
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (j k : Fin gc.configs.length)
    (hh1 : (gc.configs.get j) p ≠ (gc.configs.get k) p)
    (hrest : ∀ q : Fin sys.rs.n, q ≠ p →
      (gc.configs.get j) q = (gc.configs.get k) q)
    (q : Fin sys.rs.n) (hq : q ≠ p)
    (hm : sys.rs.m q ∈ ({2, 3} : Set Nat))
    (hfc_eq_m : gc.fireCount q = sys.rs.m q)
    (hjk : j.val < k.val) :
    gc.intervalFireCount q j.val k.val = 0 ∨
      gc.intervalFireCount q j.val k.val = sys.rs.m q := by
  set a := gc.intervalFireCount q j.val k.val with ha_def
  -- a ≤ m_q (sub-interval of full cycle)
  have ha_le : a ≤ sys.rs.m q := by
    -- ifc(j,k) + ifc(k,CL) = ifc(j,CL) ≤ ifc(0,CL) = fc(q) = m_q
    have hsplit := intervalFireCount_split gc q
      (show j.val ≤ k.val by omega)
      (show k.val ≤ gc.configs.length from Nat.le_of_lt k.isLt)
    -- hsplit: ifc(j,CL) = ifc(j,k) + ifc(k,CL), i.e., ifc(j,CL) ≥ a
    -- Also: ifc(0,j) + ifc(j,CL) = ifc(0,CL) = fc(q) = m_q
    have hsplit0 := intervalFireCount_split gc q
      (show 0 ≤ j.val by omega)
      (show j.val ≤ gc.configs.length from Nat.le_of_lt j.isLt)
    -- hsplit0: ifc(0,CL) = ifc(0,j) + ifc(j,CL)
    have hfc_eq : gc.intervalFireCount q 0 gc.configs.length = gc.fireCount q := by
      simp [GoodCycle.intervalFireCount, GoodCycle.fireCount, GoodCycle.prefixFireCount]
    rw [hfc_eq_m] at hfc_eq
    omega
  -- configs j q = configs k q (from hrest)
  have hval_eq := hrest q hq
  -- Case split: a = 0 or a = m_q or 0 < a < m_q
  by_cases h0 : a = 0
  · exact Or.inl h0
  by_cases hm_eq : a = sys.rs.m q
  · exact Or.inr hm_eq
  -- 0 < a < m_q: derive contradiction
  exfalso
  have ha_pos : 0 < a := by omega
  have ha_lt : a < sys.rs.m q := by omega
  -- With m_q ∈ {2,3} and 0 < a < m_q: a = 1, or (m_q = 3 and a = 2)
  have hm23 : sys.rs.m q = 2 ∨ sys.rs.m q = 3 := by
    simp [Set.mem_insert_iff, Set.mem_singleton_iff] at hm; exact hm
  rcases hm23 with hm2 | hm3
  · -- m_q = 2, a = 1: one fire changes value, contradicts hval_eq
    have ha1 : gc.intervalFireCount q j.val k.val = 1 := by omega
    exact (value_ne_of_single_fire gc q j.val k.val hjk k.isLt ha1) hval_eq
  · -- m_q = 3, a ∈ {1, 2}
    by_cases ha1 : a = 1
    · -- a = 1: same as binary case
      have : gc.intervalFireCount q j.val k.val = 1 := by omega
      exact (value_ne_of_single_fire gc q j.val k.val hjk k.isLt this) hval_eq
    · -- a = 2, m_q = 3: complement [0,j)∪[k,CL) has 3-2 = 1 fire.
      -- Complement fire count
      have hcompl : gc.intervalFireCount q 0 j.val +
          gc.intervalFireCount q k.val gc.configs.length = 1 := by
        have := intervalFireCount_split gc q (show j.val ≤ k.val by omega)
          (show k.val ≤ gc.configs.length from Nat.le_of_lt k.isLt)
        have := intervalFireCount_split gc q (show 0 ≤ j.val by omega)
          (show j.val ≤ gc.configs.length from Nat.le_of_lt j.isLt)
        have : gc.intervalFireCount q 0 gc.configs.length = gc.fireCount q := by
          simp [GoodCycle.intervalFireCount, GoodCycle.fireCount, GoodCycle.prefixFireCount]
        rw [hfc_eq_m, hm3] at this; omega
      -- Helper: ifc=0 → no fires (for stateAfter_eq_of_no_fire)
      have nofire_of_ifc0 : ∀ a' b' : Nat, a' ≤ b' → b' ≤ gc.configs.length →
          gc.intervalFireCount q a' b' = 0 →
          ∀ s : Fin gc.configs.length, a' ≤ s.val → s.val < b' → gc.moverAt s ≠ q := by
        intro a' b' hab' hb' hifc0 s hs1 hs2 hm
        have := intervalFireCount_split gc q (show a' ≤ s.val from hs1) (show s.val ≤ b' by omega)
        have := intervalFireCount_split gc q (show s.val ≤ s.val + 1 by omega)
          (show s.val + 1 ≤ b' by omega)
        have : gc.intervalFireCount q s.val (s.val + 1) ≥ 1 := by
          simp only [GoodCycle.intervalFireCount, GoodCycle.prefixFireCount,
            Finset.sum_range_succ, Finset.sum_range_zero]
          simp [GoodCycle.fireIndicator, s.isLt, hm]
        omega
      by_cases h0j_pos : gc.intervalFireCount q 0 j.val ≥ 1
      · -- 1 fire in [0,j), 0 in [k,CL)
        have hkCL0 : gc.intervalFireCount q k.val gc.configs.length = 0 := by omega
        have hj_pos : 0 < j.val := by
          by_contra hj0; push_neg at hj0
          have hj0' : j.val = 0 := by omega
          have : gc.intervalFireCount q 0 j.val = 0 := by
            rw [hj0']; simp [GoodCycle.intervalFireCount]
          omega
        have hne_0j := value_ne_of_single_fire gc q 0 j.val hj_pos j.isLt (by omega)
        -- 0 fires in [k,CL) → stateAfter CL = stateAfter k
        have hchain := gc.stateAfter_eq_of_no_fire q (Nat.le_of_lt k.isLt) le_rfl
          (nofire_of_ifc0 k.val gc.configs.length (Nat.le_of_lt k.isLt) le_rfl hkCL0)
        rw [stateAfter_length_eq_config0, gc.stateAfter_of_lt q k.isLt] at hchain
        -- hchain : configs 0 q = configs k q. hval_eq : configs j q = configs k q.
        -- hne_0j : configs 0 q ≠ configs j q.
        exact hne_0j (hchain.trans hval_eq.symm)
      · -- 0 fires in [0,j), 1 fire in [k,CL)
        push_neg at h0j_pos
        have h0j0 : gc.intervalFireCount q 0 j.val = 0 := by omega
        have hkCL1 : gc.intervalFireCount q k.val gc.configs.length = 1 := by omega
        -- configs 0 = configs j (no fires)
        have h0j := configVal_eq_of_noFire_between gc q 0 j.val (by omega) j.isLt
          (nofire_of_ifc0 0 j.val (by omega) (Nat.le_of_lt j.isLt) h0j0)
        -- stateAfter CL ≠ stateAfter k (1 fire in [k,CL))
        have hne := stateAfter_ne_of_single_fire_to_end gc q k.val k.isLt hkCL1
        apply hne
        rw [stateAfter_length_eq_config0, gc.stateAfter_of_lt q k.isLt, h0j, hval_eq]

/-! ### Note: H-1 Uniqueness is FALSE

    PA (2026-04-07) found counterexamples at n=3, ms=(2,3,3): consecutive
    ternary fires create non-adjacent Hamming-1 pairs. The gcd_obstruction
    and h1_uniqueness theorems that were here have been REMOVED.

    The sweep non-consecutive case now uses Binary Flip Shadow EC instead
    (see ShadowOrbit.lean). H-1 Uniqueness is not needed.

    The proved infrastructure above (value_coverage, arc_return, stateAfter
    helpers, sum lemmas) is all correct and may be useful elsewhere. -/

end LeanMn
