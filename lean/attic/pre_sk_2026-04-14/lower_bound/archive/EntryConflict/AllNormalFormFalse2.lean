import LeanMn.LowerBound.EntryConflict.PhaseExtractionBase
import LeanMn.LowerBound.EntryConflict.ContextBridge
import LeanMn.LowerBound.EntryConflict.BinaryParity

namespace LeanMn

variable {sys : System}

/-! ### Layer 2: Within-phase entry conflict at a neighbor of t.

Given a t-phase where a second-neighbor (left²t or right²t) doesn't fire,
and the first firing of the corresponding first-neighbor (left t or right t)
has a gap after the t-firing (non-tight), derive entry conflict. -/

/-- Non-tight within-phase EC at left t.
    Given step `f` = first left-t firing in the phase, with `f > phase.a + 1`:
    the boundary triple at left t is constant from `phase.a + 1` to `f`,
    and step `f` is a left-t mover while step `phase.a + 1` is not. -/
private theorem within_phase_ec_left
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    -- f is a step in the phase where left t fires
    (f : Fin gc.configs.length)
    (hf_range : phase.a.val < f.val ∧ f.val < phase.s.val)
    (hf_mover : gc.moverAt f = left t)
    -- No left t firing between phase.a and f (f is first)
    (hf_first : ∀ k : Fin gc.configs.length,
      phase.a.val < k.val → k.val < f.val → gc.moverAt k ≠ left t)
    -- left²t doesn't fire in the phase
    (h_no_left2 : ∀ k : Fin gc.configs.length,
      phase.a.val < k.val → k.val < phase.s.val →
      gc.moverAt k ≠ left (left t))
    -- Non-tight: there's a gap between the t-firing and the first left-t firing
    (hf_gap : f.val > phase.a.val + 1) :
    False := by
  -- Step a+1 exists
  have ha1_lt : phase.a.val + 1 < gc.configs.length := by
    have := phase.ha_lt_s; have := phase.s.isLt; omega
  set a1 : Fin gc.configs.length := ⟨phase.a.val + 1, ha1_lt⟩
  -- moverAt(a+1) ≠ left t (f is the first left-t firing, f > a+1)
  have ha1_ne : gc.moverAt a1 ≠ left t :=
    hf_first a1 (by show phase.a.val < a1.val; simp [a1]) (by show a1.val < f.val; simp [a1]; omega)
  -- Between a+1 and f: no fires of left²t, left t, or t
  -- → boundary triple at left t is constant
  -- Between a1 and f: no fires of left²t, left t, or t
  have ha1_val : a1.val = phase.a.val + 1 := rfl
  have hL_eq := configVal_eq_of_noFire_between gc (left (left t))
      a1.val f.val (by omega) f.isLt
      (fun k hk1 hk2 => h_no_left2 k (by omega) (by omega))
  have hS_eq := configVal_eq_of_noFire_between gc (left t)
      a1.val f.val (by omega) f.isLt
      (fun k hk1 hk2 => hf_first k (by omega) hk2)
  have hrl : right (left t) = t := right_left_eq_self t
  have hR_eq := configVal_eq_of_noFire_between gc (right (left t))
      a1.val f.val (by omega) f.isLt
      (fun k hk1 hk2 => by rw [hrl]; exact phase.ht_nofire k (by omega) (by omega))
  -- Entry conflict at left t: step f (mover) vs step a1 (non-mover)
  exact entryConflict_impossible gc
    ⟨f, a1, left t, hf_mover, ha1_ne,
      hL_eq.symm, hS_eq.symm, hR_eq.symm⟩

/-- Symmetric: non-tight within-phase EC at right t. -/
private theorem within_phase_ec_right
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (f : Fin gc.configs.length)
    (hf_range : phase.a.val < f.val ∧ f.val < phase.s.val)
    (hf_mover : gc.moverAt f = right t)
    (hf_first : ∀ k : Fin gc.configs.length,
      phase.a.val < k.val → k.val < f.val → gc.moverAt k ≠ right t)
    (h_no_right2 : ∀ k : Fin gc.configs.length,
      phase.a.val < k.val → k.val < phase.s.val →
      gc.moverAt k ≠ right (right t))
    (hf_gap : f.val > phase.a.val + 1) :
    False := by
  have ha1_lt : phase.a.val + 1 < gc.configs.length := by
    have := phase.ha_lt_s; have := phase.s.isLt; omega
  set a1 : Fin gc.configs.length := ⟨phase.a.val + 1, ha1_lt⟩
  have ha1_ne : gc.moverAt a1 ≠ right t :=
    hf_first a1 (by show phase.a.val < a1.val; simp [a1]) (by show a1.val < f.val; simp [a1]; omega)
  have ha1_val : a1.val = phase.a.val + 1 := rfl
  have hlr : left (right t) = t := left_right_eq_self t
  have hL_eq := configVal_eq_of_noFire_between gc (left (right t))
      a1.val f.val (by omega) f.isLt
      (fun k hk1 hk2 => by rw [hlr]; exact phase.ht_nofire k (by omega) (by omega))
  have hS_eq := configVal_eq_of_noFire_between gc (right t)
      a1.val f.val (by omega) f.isLt
      (fun k hk1 hk2 => hf_first k (by omega) hk2)
  have hR_eq := configVal_eq_of_noFire_between gc (right (right t))
      a1.val f.val (by omega) f.isLt
      (fun k hk1 hk2 => h_no_right2 k (by omega) (by omega))
  exact entryConflict_impossible gc
    ⟨f, a1, right t, hf_mover, ha1_ne,
      hL_eq.symm, hS_eq.symm, hR_eq.symm⟩

/-- Given a strict firing of `p` inside `(a, b)`, pick the first such firing. -/
private theorem exists_first_strict_fire
    (gc : GoodCycle sys) (p : Fin sys.rs.n) (a b : Nat)
    (hex : ∃ k : Fin gc.configs.length,
      a < k.val ∧ k.val < b ∧ gc.moverAt k = p) :
    ∃ k : Fin gc.configs.length,
      a < k.val ∧ k.val < b ∧ gc.moverAt k = p ∧
      ∀ j : Fin gc.configs.length,
        a < j.val → j.val < k.val → gc.moverAt j ≠ p := by
  classical
  let S := (Finset.univ : Finset (Fin gc.configs.length)).filter
    (fun k => a < k.val ∧ k.val < b ∧ gc.moverAt k = p)
  have hne : S.Nonempty := by
    rcases hex with ⟨k, hka, hkb, hkm⟩
    exact ⟨k, by simp [S, hka, hkb, hkm]⟩
  let kmin := S.min' hne
  have hkmin_mem : kmin ∈ S := Finset.min'_mem S hne
  have hkmin_le :
      ∀ j : Fin gc.configs.length, j ∈ S → kmin.val ≤ j.val := by
    intro j hj
    exact Finset.min'_le S j hj
  have hkmin_data : a < kmin.val ∧ kmin.val < b ∧ gc.moverAt kmin = p := by
    simpa [S, kmin] using hkmin_mem
  rcases hkmin_data with ⟨hka, hkb, hkm⟩
  refine ⟨kmin, hka, hkb, hkm, ?_⟩
  intro j hja hjk hjm
  have hj_mem : j ∈ S := by
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_univ j, ?_⟩
    exact ⟨hja, by omega, hjm⟩
  have := hkmin_le j hj_mem
  omega

/-- A single-step interval has fire count at most 1. -/
private theorem intervalFireCount_single_eq
    (gc : GoodCycle sys) (p : Fin sys.rs.n) (k : Nat) (hk : k < gc.configs.length) :
    gc.intervalFireCount p k (k + 1) = if gc.moverAt ⟨k, hk⟩ = p then 1 else 0 := by
  unfold GoodCycle.intervalFireCount GoodCycle.prefixFireCount
  rw [Finset.sum_range_succ]
  simp [GoodCycle.fireIndicator, hk]

/-- Non-strict variant: given a firing of `p` in `[a, b)`, pick the first. -/
private theorem exists_first_fire
    (gc : GoodCycle sys) (p : Fin sys.rs.n) (a b : Nat)
    (hex : ∃ k : Fin gc.configs.length,
      a ≤ k.val ∧ k.val < b ∧ gc.moverAt k = p) :
    ∃ k : Fin gc.configs.length,
      a ≤ k.val ∧ k.val < b ∧ gc.moverAt k = p ∧
      ∀ j : Fin gc.configs.length,
        a ≤ j.val → j.val < k.val → gc.moverAt j ≠ p := by
  classical
  let S := (Finset.univ : Finset (Fin gc.configs.length)).filter
    (fun k => a ≤ k.val ∧ k.val < b ∧ gc.moverAt k = p)
  have hne : S.Nonempty := by
    rcases hex with ⟨k, hka, hkb, hkm⟩
    exact ⟨k, by simp [S, hka, hkb, hkm]⟩
  let kmin := S.min' hne
  have hkmin_mem : kmin ∈ S := Finset.min'_mem S hne
  have hkmin_le :
      ∀ j : Fin gc.configs.length, j ∈ S → kmin.val ≤ j.val := by
    intro j hj
    exact Finset.min'_le S j hj
  have hkmin_data : a ≤ kmin.val ∧ kmin.val < b ∧ gc.moverAt kmin = p := by
    simpa [S, kmin] using hkmin_mem
  rcases hkmin_data with ⟨hka, hkb, hkm⟩
  refine ⟨kmin, hka, hkb, hkm, ?_⟩
  intro j hja hjk hjm
  have hj_mem : j ∈ S := by
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_univ j, ?_⟩
    exact ⟨hja, by omega, hjm⟩
  have := hkmin_le j hj_mem
  omega

/-- Given a firing of `p` in `[a, b)`, pick the last. -/
private theorem exists_last_fire
    (gc : GoodCycle sys) (p : Fin sys.rs.n) (a b : Nat)
    (hex : ∃ k : Fin gc.configs.length,
      a ≤ k.val ∧ k.val < b ∧ gc.moverAt k = p) :
    ∃ k : Fin gc.configs.length,
      a ≤ k.val ∧ k.val < b ∧ gc.moverAt k = p ∧
      ∀ j : Fin gc.configs.length,
        k.val < j.val → j.val < b → gc.moverAt j ≠ p := by
  classical
  let S := (Finset.univ : Finset (Fin gc.configs.length)).filter
    (fun k => a ≤ k.val ∧ k.val < b ∧ gc.moverAt k = p)
  have hne : S.Nonempty := by
    rcases hex with ⟨k, hka, hkb, hkm⟩
    exact ⟨k, by simp [S, hka, hkb, hkm]⟩
  let kmax := S.max' hne
  have hkmax_mem : kmax ∈ S := Finset.max'_mem S hne
  have hkmax_ge :
      ∀ j : Fin gc.configs.length, j ∈ S → j.val ≤ kmax.val := by
    intro j hj; exact Finset.le_max' S j hj
  have hkmax_data : a ≤ kmax.val ∧ kmax.val < b ∧ gc.moverAt kmax = p := by
    simpa [S, kmax] using hkmax_mem
  rcases hkmax_data with ⟨hka, hkb, hkm⟩
  refine ⟨kmax, hka, hkb, hkm, ?_⟩
  intro j hjk hjb hjm
  have hj_mem : j ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_univ j, by omega, hjb, hjm⟩
  have := hkmax_ge j hj_mem; omega

/-- Tight free-left phase: if the remaining number of `left t` fires from
    `phase.a + 1` to `phase.s` is even, then `left t` sees the same boundary
    context at the mover step `a+1` and the non-mover `t`-step `phase.s`. -/
private theorem tight_even_left_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hbL : sys.rs.m (left t) = 2)
    (h_no_left2 : ∀ k : Fin gc.configs.length,
      phase.a.val < k.val → k.val < phase.s.val →
      gc.moverAt k ≠ left (left t))
    (a1 : Fin gc.configs.length)
    (ha1 : a1.val = phase.a.val + 1)
    (ha1_left : gc.moverAt a1 = left t)
    (h_even : Even (gc.intervalFireCount (left t) a1.val phase.s.val)) :
    False := by
  have hlt_ne_t : left t ≠ t := by
    intro h
    have := congrArg Fin.val h
    simp only [left_val] at this
    have hn := sys.rs.n_ge_4
    have ht := t.isLt
    by_cases h0 : t.val = 0
    · rw [h0] at this
      simp at this
      omega
    · rw [show t.val + sys.rs.n - 1 = (t.val - 1) + sys.rs.n from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at this
      omega
  have hs_ne_left : gc.moverAt phase.s ≠ left t := by
    intro hs_left
    apply hlt_ne_t
    calc
      left t = gc.moverAt phase.s := hs_left.symm
      _ = t := phase.hs_mover
  have ha1_ne_s : a1 ≠ phase.s := by
    intro hEq
    exact hs_ne_left (by simpa [hEq] using ha1_left)
  have ha1_lt_s : a1.val < phase.s.val := by
    have hle : a1.val ≤ phase.s.val := by
      rw [ha1]
      exact Nat.succ_le_of_lt phase.ha_lt_s
    exact lt_of_le_of_ne hle (by
      intro hEq
      exact ha1_ne_s (Fin.ext hEq))
  have hLL_eq := configVal_eq_of_noFire_between gc (left (left t))
      a1.val phase.s.val (Nat.le_of_lt ha1_lt_s) phase.s.isLt
      (fun k hk1 hk2 => h_no_left2 k (by
        rw [ha1] at hk1
        omega) hk2)
  have hS_eq := binary_config_eq_of_even_intervalFireCount gc (left t) hbL
      a1.val phase.s.val (Nat.le_of_lt ha1_lt_s) phase.s.isLt h_even
  have hR_eq := configVal_eq_of_noFire_between gc (right (left t))
      a1.val phase.s.val (Nat.le_of_lt ha1_lt_s) phase.s.isLt
      (fun k hk1 hk2 => by
        rw [right_left_eq_self]
        exact phase.ht_nofire k (by
          rw [ha1] at hk1
          omega) hk2)
  exact entryConflict_impossible gc
    ⟨a1, phase.s, left t, ha1_left, hs_ne_left, hLL_eq, hS_eq, hR_eq⟩

/-- Symmetric tight free-right even-parity entry conflict. -/
private theorem tight_even_right_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hbR : sys.rs.m (right t) = 2)
    (h_no_right2 : ∀ k : Fin gc.configs.length,
      phase.a.val < k.val → k.val < phase.s.val →
      gc.moverAt k ≠ right (right t))
    (a1 : Fin gc.configs.length)
    (ha1 : a1.val = phase.a.val + 1)
    (ha1_right : gc.moverAt a1 = right t)
    (h_even : Even (gc.intervalFireCount (right t) a1.val phase.s.val)) :
    False := by
  have hrt_ne_t : right t ≠ t := by
    intro h
    have hval := congrArg Fin.val h
    simp only [right, Fin.val_mk] at hval
    have hn := sys.rs.n_ge_4
    have ht := t.isLt
    by_cases htop : t.val + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt htop] at hval
      omega
    · have : t.val = sys.rs.n - 1 := by omega
      rw [this, show sys.rs.n - 1 + 1 = sys.rs.n from by omega, Nat.mod_self] at hval
      omega
  have hs_ne_right : gc.moverAt phase.s ≠ right t := by
    intro hs_right
    apply hrt_ne_t
    calc
      right t = gc.moverAt phase.s := hs_right.symm
      _ = t := phase.hs_mover
  have ha1_ne_s : a1 ≠ phase.s := by
    intro hEq
    exact hs_ne_right (by simpa [hEq] using ha1_right)
  have ha1_lt_s : a1.val < phase.s.val := by
    have hle : a1.val ≤ phase.s.val := by
      rw [ha1]
      exact Nat.succ_le_of_lt phase.ha_lt_s
    exact lt_of_le_of_ne hle (by
      intro hEq
      exact ha1_ne_s (Fin.ext hEq))
  have hL_eq := configVal_eq_of_noFire_between gc (left (right t))
      a1.val phase.s.val (Nat.le_of_lt ha1_lt_s) phase.s.isLt
      (fun k hk1 hk2 => by
        rw [left_right_eq_self]
        exact phase.ht_nofire k (by
          rw [ha1] at hk1
          omega) hk2)
  have hS_eq := binary_config_eq_of_even_intervalFireCount gc (right t) hbR
      a1.val phase.s.val (Nat.le_of_lt ha1_lt_s) phase.s.isLt h_even
  have hR_eq := configVal_eq_of_noFire_between gc (right (right t))
      a1.val phase.s.val (Nat.le_of_lt ha1_lt_s) phase.s.isLt
      (fun k hk1 hk2 => h_no_right2 k (by
        rw [ha1] at hk1
        omega) hk2)
  exact entryConflict_impossible gc
    ⟨a1, phase.s, right t, ha1_right, hs_ne_right, hL_eq, hS_eq, hR_eq⟩

/-- Entry conflict from Case C (both sides fire): if left t fires at step q
    and right t fires at step u with q < u, and no t, right t, or right²t fires
    in between, then the boundary triple at right t is preserved from q to u,
    giving EC at right t (mover u vs non-mover q). -/
private theorem ec_caseC_LR
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (q u : Fin gc.configs.length)
    (hq : gc.moverAt q = left t)
    (hu : gc.moverAt u = right t)
    (hqu : q.val < u.val)
    (hnoT : ∀ k : Fin gc.configs.length,
      q.val ≤ k.val → k.val < u.val → gc.moverAt k ≠ t)
    (hnoR : ∀ k : Fin gc.configs.length,
      q.val ≤ k.val → k.val < u.val → gc.moverAt k ≠ right t)
    (hnoRR : ∀ k : Fin gc.configs.length,
      q.val ≤ k.val → k.val < u.val → gc.moverAt k ≠ right (right t)) :
    hasEntryConflict gc := by
  -- The boundary triple at (right t) is (left (right t), right t, right (right t))
  -- = (t, right t, right²t) after rewriting left_right_eq_self.
  -- None of t, right t, right²t fire in [q, u), so configs are preserved.
  have hlr : left (right t) = t := left_right_eq_self t
  have hL_eq := configVal_eq_of_noFire_between gc (left (right t))
      q.val u.val (Nat.le_of_lt hqu) u.isLt
      (fun k hk1 hk2 => by rw [hlr]; exact hnoT k hk1 hk2)
  have hS_eq := configVal_eq_of_noFire_between gc (right t)
      q.val u.val (Nat.le_of_lt hqu) u.isLt
      (fun k hk1 hk2 => hnoR k hk1 hk2)
  have hR_eq := configVal_eq_of_noFire_between gc (right (right t))
      q.val u.val (Nat.le_of_lt hqu) u.isLt
      (fun k hk1 hk2 => hnoRR k hk1 hk2)
  -- moverAt u = right t, moverAt q = left t ≠ right t
  have hq_ne : gc.moverAt q ≠ right t := by
    rw [hq]
    intro h
    have hval := congrArg Fin.val h
    simp only [left_val, right_val] at hval
    have hn := sys.rs.n_ge_4
    have hi := t.isLt
    by_cases h0 : t.val = 0
    · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at hval
      omega
    · by_cases hlt : t.val + 1 < sys.rs.n
      · rw [Nat.mod_eq_of_lt hlt] at hval
        rw [show t.val + sys.rs.n - 1 = (t.val - 1) + sys.rs.n by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hval
        omega
      · rw [show t.val + 1 = sys.rs.n by omega, Nat.mod_self] at hval
        rw [show t.val + sys.rs.n - 1 = (t.val - 1) + sys.rs.n by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hval
        omega
  exact ⟨u, q, right t, hu, hq_ne, hL_eq.symm, hS_eq.symm, hR_eq.symm⟩

/-- Symmetric: right t fires first at q, left t fires at u with q < u,
    no t, left t, or left²t fires in between → EC at left t. -/
private theorem ec_caseC_RL
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (q u : Fin gc.configs.length)
    (hq : gc.moverAt q = right t)
    (hu : gc.moverAt u = left t)
    (hqu : q.val < u.val)
    (hnoT : ∀ k : Fin gc.configs.length,
      q.val ≤ k.val → k.val < u.val → gc.moverAt k ≠ t)
    (hnoL : ∀ k : Fin gc.configs.length,
      q.val ≤ k.val → k.val < u.val → gc.moverAt k ≠ left t)
    (hnoLL : ∀ k : Fin gc.configs.length,
      q.val ≤ k.val → k.val < u.val → gc.moverAt k ≠ left (left t)) :
    hasEntryConflict gc := by
  have hrl : right (left t) = t := right_left_eq_self t
  have hL_eq := configVal_eq_of_noFire_between gc (left (left t))
      q.val u.val (Nat.le_of_lt hqu) u.isLt
      (fun k hk1 hk2 => hnoLL k hk1 hk2)
  have hS_eq := configVal_eq_of_noFire_between gc (left t)
      q.val u.val (Nat.le_of_lt hqu) u.isLt
      (fun k hk1 hk2 => hnoL k hk1 hk2)
  have hR_eq := configVal_eq_of_noFire_between gc (right (left t))
      q.val u.val (Nat.le_of_lt hqu) u.isLt
      (fun k hk1 hk2 => by rw [hrl]; exact hnoT k hk1 hk2)
  have hq_ne : gc.moverAt q ≠ left t := by
    rw [hq]
    intro h
    have hval := congrArg Fin.val h
    simp only [left_val, right_val] at hval
    have hn := sys.rs.n_ge_4
    have hi := t.isLt
    by_cases h0 : t.val = 0
    · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at hval
      omega
    · by_cases hlt : t.val + 1 < sys.rs.n
      · rw [Nat.mod_eq_of_lt hlt] at hval
        rw [show t.val + sys.rs.n - 1 = (t.val - 1) + sys.rs.n by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hval
        omega
      · rw [show t.val + 1 = sys.rs.n by omega, Nat.mod_self] at hval
        rw [show t.val + sys.rs.n - 1 = (t.val - 1) + sys.rs.n by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hval
        omega
  exact ⟨u, q, left t, hu, hq_ne, hL_eq.symm, hS_eq.symm, hR_eq.symm⟩

/-- Case A: J ≥ 2. Binary recovery via parity-chosen L-fire.
    On [q, b): no LL fires, no t fires, and L fires an even number of times.
    So boundary triple at L = (LL, L, t) is preserved. EC at L. -/
private lemma ec_caseA
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2)
    (q b : Fin gc.configs.length)
    (hqb : q.val < b.val)
    (hmq : gc.moverAt q = left t)
    (hnb : gc.moverAt b ≠ left t)
    -- No LL fires in [q, b)
    (hnoLL : ∀ k : Fin gc.configs.length,
      q.val ≤ k.val → k.val < b.val → gc.moverAt k ≠ left (left t))
    -- No t fires in [q, b)
    (hnoT : ∀ k : Fin gc.configs.length,
      q.val ≤ k.val → k.val < b.val → gc.moverAt k ≠ t)
    -- Even number of L fires in [q, b)
    (heven : Even (gc.intervalFireCount (left t) q.val b.val)) :
    hasEntryConflict gc := by
  have hrl : right (left t) = t := right_left_eq_self t
  -- config[left²t] preserved: no LL fires
  have hL : (gc.configs.get ⟨q.val, q.isLt⟩) (left (left t)) =
      (gc.configs.get ⟨b.val, b.isLt⟩) (left (left t)) :=
    configVal_eq_of_noFire_between gc (left (left t)) q.val b.val
      (Nat.le_of_lt hqb) b.isLt
      (fun k hk1 hk2 => hnoLL k hk1 hk2)
  -- config[left t] preserved: even L fires (binary parity)
  have hS : (gc.configs.get ⟨q.val, q.isLt⟩) (left t) =
      (gc.configs.get ⟨b.val, b.isLt⟩) (left t) :=
    binary_config_eq_of_even_intervalFireCount gc (left t) hbL
      q.val b.val (Nat.le_of_lt hqb) b.isLt heven
  -- config[t] preserved: no t fires (right (left t) = t)
  have hR : (gc.configs.get ⟨q.val, q.isLt⟩) (right (left t)) =
      (gc.configs.get ⟨b.val, b.isLt⟩) (right (left t)) := by
    rw [hrl]
    exact configVal_eq_of_noFire_between gc t q.val b.val
      (Nat.le_of_lt hqb) b.isLt
      (fun k hk1 hk2 => hnoT k hk1 hk2)
  exact ⟨q, b, left t, hmq, hnb, hL, hS, hR⟩

/-- Case B (symmetric): K ≥ 2. Binary recovery via parity-chosen R-fire.
    On [q, b): no RR fires, no t fires, and R fires an even number of times.
    So boundary triple at R = (t, R, RR) is preserved. EC at R. -/
private lemma ec_caseB
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbR : sys.rs.m (right t) = 2)
    (q b : Fin gc.configs.length)
    (hqb : q.val < b.val)
    (hmq : gc.moverAt q = right t)
    (hnb : gc.moverAt b ≠ right t)
    -- No RR fires in [q, b)
    (hnoRR : ∀ k : Fin gc.configs.length,
      q.val ≤ k.val → k.val < b.val → gc.moverAt k ≠ right (right t))
    -- No t fires in [q, b)
    (hnoT : ∀ k : Fin gc.configs.length,
      q.val ≤ k.val → k.val < b.val → gc.moverAt k ≠ t)
    -- Even number of R fires in [q, b)
    (heven : Even (gc.intervalFireCount (right t) q.val b.val)) :
    hasEntryConflict gc := by
  have hlr : left (right t) = t := left_right_eq_self t
  -- config[t] preserved: no t fires (left (right t) = t)
  have hL : (gc.configs.get ⟨q.val, q.isLt⟩) (left (right t)) =
      (gc.configs.get ⟨b.val, b.isLt⟩) (left (right t)) := by
    rw [hlr]
    exact configVal_eq_of_noFire_between gc t q.val b.val
      (Nat.le_of_lt hqb) b.isLt
      (fun k hk1 hk2 => hnoT k hk1 hk2)
  -- config[right t] preserved: even R fires (binary parity)
  have hS : (gc.configs.get ⟨q.val, q.isLt⟩) (right t) =
      (gc.configs.get ⟨b.val, b.isLt⟩) (right t) :=
    binary_config_eq_of_even_intervalFireCount gc (right t) hbR
      q.val b.val (Nat.le_of_lt hqb) b.isLt heven
  -- config[right²t] preserved: no RR fires
  have hR : (gc.configs.get ⟨q.val, q.isLt⟩) (right (right t)) =
      (gc.configs.get ⟨b.val, b.isLt⟩) (right (right t)) :=
    configVal_eq_of_noFire_between gc (right (right t)) q.val b.val
      (Nat.le_of_lt hqb) b.isLt
      (fun k hk1 hk2 => hnoRR k hk1 hk2)
  exact ⟨q, b, right t, hmq, hnb, hL, hS, hR⟩

private lemma rr_ne_l
    (hn : sys.rs.n ≥ 4) (t : Fin sys.rs.n) :
    right (right t) ≠ left t := by
  intro h
  have hval := congrArg Fin.val h
  have hi : t.val < sys.rs.n := t.isLt
  by_cases h0 : t.val = 0
  · have hR1 : (right t).val = 1 := by
      rw [right_val, h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    have hRR : (right (right t)).val = 2 := by
      rw [right_val, hR1, Nat.mod_eq_of_lt (by omega)]
    have hL : (left t).val = sys.rs.n - 1 := by
      rw [left_val, h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [hRR, hL] at hval
    omega
  · have hL : (left t).val = t.val - 1 := by
      rw [left_val,
        show t.val + sys.rs.n - 1 = (t.val - 1) + sys.rs.n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    by_cases h1 : t.val + 1 < sys.rs.n
    · have hR1 : (right t).val = t.val + 1 := by
        rw [right_val, Nat.mod_eq_of_lt h1]
      by_cases h2 : t.val + 2 < sys.rs.n
      · have hRR : (right (right t)).val = t.val + 2 := by
          rw [right_val, hR1, Nat.mod_eq_of_lt h2]
        rw [hRR, hL] at hval
        omega
      · have h2eq : t.val + 2 = sys.rs.n := by omega
        have hRR : (right (right t)).val = 0 := by
          rw [right_val, hR1, h2eq, Nat.mod_self]
        rw [hRR, hL] at hval
        omega
    · have h1eq : t.val + 1 = sys.rs.n := by omega
      have hR1 : (right t).val = 0 := by
        rw [right_val, h1eq, Nat.mod_self]
      have hRR : (right (right t)).val = 1 := by
        rw [right_val, hR1, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      rw [hRR, hL] at hval
      omega

private lemma rr_ne_ll
    (hn : sys.rs.n ≥ 5) (t : Fin sys.rs.n) :
    right (right t) ≠ left (left t) := by
  intro h
  have hval := congrArg Fin.val h
  have hi : t.val < sys.rs.n := t.isLt
  by_cases h0 : t.val = 0
  · have hR1 : (right t).val = 1 := by
      rw [right_val, h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    have hRR : (right (right t)).val = 2 := by
      rw [right_val, hR1, Nat.mod_eq_of_lt (by omega)]
    have hL1 : (left t).val = sys.rs.n - 1 := by
      rw [left_val, h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    have hLL : (left (left t)).val = sys.rs.n - 2 := by
      rw [left_val, hL1,
        show sys.rs.n - 1 + sys.rs.n - 1 = (sys.rs.n - 2) + sys.rs.n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hRR, hLL] at hval
    omega
  · by_cases h1 : t.val = 1
    · have hR1 : (right t).val = 2 := by
        rw [right_val, h1, Nat.mod_eq_of_lt (by omega)]
      have hRR : (right (right t)).val = 3 := by
        rw [right_val, hR1, Nat.mod_eq_of_lt (by omega)]
      have hL1 : (left t).val = 0 := by
        rw [left_val, h1,
          show 1 + sys.rs.n - 1 = sys.rs.n by omega,
          Nat.mod_self]
      have hLL : (left (left t)).val = sys.rs.n - 1 := by
        rw [left_val, hL1, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      rw [hRR, hLL] at hval
      omega
    · have hL1 : (left t).val = t.val - 1 := by
        rw [left_val,
          show t.val + sys.rs.n - 1 = (t.val - 1) + sys.rs.n by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hLL : (left (left t)).val = t.val - 2 := by
        rw [left_val, hL1,
          show (t.val - 1) + sys.rs.n - 1 = (t.val - 2) + sys.rs.n by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      by_cases h2 : t.val + 2 < sys.rs.n
      · have hR1 : (right t).val = t.val + 1 := by
          have : t.val + 1 < sys.rs.n := by omega
          rw [right_val, Nat.mod_eq_of_lt this]
        have hRR : (right (right t)).val = t.val + 2 := by
          rw [right_val, hR1, Nat.mod_eq_of_lt h2]
        rw [hRR, hLL] at hval
        omega
      · by_cases htop : t.val + 1 < sys.rs.n
        · have h2eq : t.val + 2 = sys.rs.n := by omega
          have hR1 : (right t).val = t.val + 1 := by
            rw [right_val, Nat.mod_eq_of_lt htop]
          have hRR : (right (right t)).val = 0 := by
            rw [right_val, hR1, h2eq, Nat.mod_self]
          rw [hRR, hLL] at hval
          omega
        · have h1eq : t.val + 1 = sys.rs.n := by omega
          have hR1 : (right t).val = 0 := by
            rw [right_val, h1eq, Nat.mod_self]
          have hRR : (right (right t)).val = 1 := by
            rw [right_val, hR1, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
          rw [hRR, hLL] at hval
          omega

private lemma ll_ne_r
    (hn : sys.rs.n ≥ 4) (t : Fin sys.rs.n) :
    left (left t) ≠ right t := by
  intro h
  have h' := rr_ne_l hn (left t)
  exact h' (by simpa [right_left_eq_self] using h.symm)

private lemma ll_ne_rr
    (hn : sys.rs.n ≥ 5) (t : Fin sys.rs.n) :
    left (left t) ≠ right (right t) := by
  intro h
  exact rr_ne_ll hn t h.symm

/--
If `k₀` is the last second-neighbor fire in the phase and it is `right² t`,
then under `¬hasEntryConflict` the suffix `[k₀, phase.s)` has:
* no `left t` fires
* exactly one `right t` fire
-/
private lemma suffix_after_last_right2_sparse
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (_hn : sys.rs.n ≥ 9)
    (hnoEC : ¬hasEntryConflict gc)
    (hall_normal : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t)
    (k₀ : Fin gc.configs.length)
    (hk₀_lo : phase.a.val ≤ k₀.val)
    (hk₀_hi : k₀.val < phase.s.val)
    (hk₀_rr : gc.moverAt k₀ = right (right t))
    (hk₀_last2 : ∀ k : Fin gc.configs.length,
      k₀.val < k.val → k.val < phase.s.val →
      gc.moverAt k ≠ left (left t) ∧ gc.moverAt k ≠ right (right t)) :
    (∀ k : Fin gc.configs.length,
      k₀.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ left t) ∧
    gc.intervalFireCount (right t) k₀.val phase.s.val = 1 := by
  have hn4 : sys.rs.n ≥ 4 := by omega
  have hn5 : sys.rs.n ≥ 5 := by omega
  have hrr_ne_l : right (right t) ≠ left t := rr_ne_l hn4 t
  have hrr_ne_ll : right (right t) ≠ left (left t) := rr_ne_ll hn5 t

  have hnoL :
      ∀ k : Fin gc.configs.length,
        k₀.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ left t := by
    intro k hk1 hk2 hkL
    have hk0k : k₀.val < k.val := by
      by_contra hle
      have hEq : k = k₀ := by
        apply Fin.ext
        omega
      have : right (right t) = left t := by
        calc
          right (right t) = gc.moverAt k₀ := hk₀_rr.symm
          _ = gc.moverAt k := by simpa [hEq]
          _ = left t := hkL
      exact hrr_ne_l this
    obtain ⟨u, hu_lo, hu_hi, hu_m, hu_first⟩ :=
      exists_first_strict_fire gc (left t) k₀.val phase.s.val
        ⟨k, hk0k, hk2, hkL⟩

    have hLL_eq := configVal_eq_of_noFire_between gc (left (left t))
      k₀.val u.val (Nat.le_of_lt hu_lo) u.isLt
      (fun j hj1 hj2 => by
        by_cases hjk0 : j = k₀
        · rw [hjk0, hk₀_rr]
          exact hrr_ne_ll
        · exact (hk₀_last2 j (by omega) (lt_of_lt_of_le hj2 (Nat.le_of_lt hu_hi))).1)

    have hL_eq := configVal_eq_of_noFire_between gc (left t)
      k₀.val u.val (Nat.le_of_lt hu_lo) u.isLt
      (fun j hj1 hj2 => by
        by_cases hjk0 : j = k₀
        · rw [hjk0, hk₀_rr]
          exact hrr_ne_l
        · exact hu_first j (by omega) hj2)

    have hR_eq := configVal_eq_of_noFire_between gc (right (left t))
      k₀.val u.val (Nat.le_of_lt hu_lo) u.isLt
      (fun j hj1 hj2 => by
        rw [right_left_eq_self]
        exact phase.ht_nofire j (by omega) (lt_of_lt_of_le hj2 (Nat.le_of_lt hu_hi)))

    have hk₀_ne_L : gc.moverAt k₀ ≠ left t := by
      rw [hk₀_rr]
      exact hrr_ne_l

    exact hnoEC ⟨u, k₀, left t, hu_m, hk₀_ne_L, hLL_eq.symm, hL_eq.symm, hR_eq.symm⟩

  have hJ0 : gc.intervalFireCount (left t) k₀.val phase.s.val = 0 :=
    intervalFireCount_eq_zero_of_noFire gc (left t)
      (by omega) (Nat.le_of_lt phase.s.isLt) hnoL

  have hk₀_ne_t : gc.moverAt k₀ ≠ t := by
    rw [hk₀_rr]
    intro h
    exact absurd
      (show right t = left t by
        have := congrArg left h
        rwa [left_right_eq_self] at this)
      (right_ne_left (by omega : sys.rs.n ≥ 8) t)

  let suffix_phase : TernaryPhase gc t :=
    ⟨k₀, phase.s, hk₀_hi, phase.hs_mover, hk₀_ne_t,
      fun k hk1 hk2 => phase.ht_nofire k (le_trans hk₀_lo hk1) hk2⟩

  have hnorm := hall_normal suffix_phase
  have hconstr := normalForm_gap_constraint gc t suffix_phase hnorm
  have hK1 : gc.intervalFireCount (right t) k₀.val phase.s.val = 1 := hconstr.1 hJ0

  exact ⟨hnoL, hK1⟩

/--
Symmetric version: last second-neighbor is `left² t`.
Then the suffix `[k₀, phase.s)` has:
* no `right t` fires
* exactly one `left t` fire
-/
private lemma suffix_after_last_left2_sparse
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (_hn : sys.rs.n ≥ 9)
    (hnoEC : ¬hasEntryConflict gc)
    (hall_normal : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t)
    (k₀ : Fin gc.configs.length)
    (hk₀_lo : phase.a.val ≤ k₀.val)
    (hk₀_hi : k₀.val < phase.s.val)
    (hk₀_ll : gc.moverAt k₀ = left (left t))
    (hk₀_last2 : ∀ k : Fin gc.configs.length,
      k₀.val < k.val → k.val < phase.s.val →
      gc.moverAt k ≠ left (left t) ∧ gc.moverAt k ≠ right (right t)) :
    (∀ k : Fin gc.configs.length,
      k₀.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ right t) ∧
    gc.intervalFireCount (left t) k₀.val phase.s.val = 1 := by
  have hn4 : sys.rs.n ≥ 4 := by omega
  have hn5 : sys.rs.n ≥ 5 := by omega
  have hll_ne_r : left (left t) ≠ right t := ll_ne_r hn4 t
  have hll_ne_rr : left (left t) ≠ right (right t) := ll_ne_rr hn5 t

  have hnoR :
      ∀ k : Fin gc.configs.length,
        k₀.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ right t := by
    intro k hk1 hk2 hkR
    have hk0k : k₀.val < k.val := by
      by_contra hle
      have hEq : k = k₀ := by
        apply Fin.ext
        omega
      have : left (left t) = right t := by
        calc
          left (left t) = gc.moverAt k₀ := hk₀_ll.symm
          _ = gc.moverAt k := by simpa [hEq]
          _ = right t := hkR
      exact hll_ne_r this
    obtain ⟨u, hu_lo, hu_hi, hu_m, hu_first⟩ :=
      exists_first_strict_fire gc (right t) k₀.val phase.s.val
        ⟨k, hk0k, hk2, hkR⟩

    have hL_eq := configVal_eq_of_noFire_between gc (left (right t))
      k₀.val u.val (Nat.le_of_lt hu_lo) u.isLt
      (fun j hj1 hj2 => by
        rw [left_right_eq_self]
        exact phase.ht_nofire j (by omega) (lt_of_lt_of_le hj2 (Nat.le_of_lt hu_hi)))

    have hR_eq := configVal_eq_of_noFire_between gc (right t)
      k₀.val u.val (Nat.le_of_lt hu_lo) u.isLt
      (fun j hj1 hj2 => by
        by_cases hjk0 : j = k₀
        · rw [hjk0, hk₀_ll]
          exact hll_ne_r
        · exact hu_first j (by omega) hj2)

    have hRR_eq := configVal_eq_of_noFire_between gc (right (right t))
      k₀.val u.val (Nat.le_of_lt hu_lo) u.isLt
      (fun j hj1 hj2 => by
        by_cases hjk0 : j = k₀
        · rw [hjk0, hk₀_ll]
          exact hll_ne_rr
        · exact (hk₀_last2 j (by omega) (lt_of_lt_of_le hj2 (Nat.le_of_lt hu_hi))).2)

    have hk₀_ne_R : gc.moverAt k₀ ≠ right t := by
      rw [hk₀_ll]
      exact hll_ne_r

    exact hnoEC ⟨u, k₀, right t, hu_m, hk₀_ne_R, hL_eq.symm, hR_eq.symm, hRR_eq.symm⟩

  have hK0 : gc.intervalFireCount (right t) k₀.val phase.s.val = 0 :=
    intervalFireCount_eq_zero_of_noFire gc (right t)
      (by omega) (Nat.le_of_lt phase.s.isLt) hnoR

  have hk₀_ne_t : gc.moverAt k₀ ≠ t := by
    rw [hk₀_ll]
    intro h
    exact absurd
      (show left t = right t by
        have := congrArg right h
        rwa [right_left_eq_self] at this)
      (left_ne_right (by omega : sys.rs.n ≥ 8) t)

  let suffix_phase : TernaryPhase gc t :=
    ⟨k₀, phase.s, hk₀_hi, phase.hs_mover, hk₀_ne_t,
      fun k hk1 hk2 => phase.ht_nofire k (le_trans hk₀_lo hk1) hk2⟩

  have hnorm := hall_normal suffix_phase
  have hconstr := normalForm_gap_constraint gc t suffix_phase hnorm
  have hJ1 : gc.intervalFireCount (left t) k₀.val phase.s.val = 1 := hconstr.2.1 hK0

  exact ⟨hnoR, hJ1⟩

/-- Gap-1 lemma: if processor p fires at step k, and no processor in
    {left p, p, right p} fires at step k-1, then the boundary triple at p
    is preserved from step k-1 to step k.  Step k (mover = p) vs step k-1
    (non-mover at p) gives an entry conflict. -/
private theorem gap1_ec
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (k : Fin gc.configs.length)
    (hk_pos : 0 < k.val)
    (hk_mover : gc.moverAt k = p)
    (hprev_L : gc.moverAt ⟨k.val - 1, by omega⟩ ≠ left p)
    (hprev_S : gc.moverAt ⟨k.val - 1, by omega⟩ ≠ p)
    (hprev_R : gc.moverAt ⟨k.val - 1, by omega⟩ ≠ right p) :
    hasEntryConflict gc := by
  set prev : Fin gc.configs.length := ⟨k.val - 1, by omega⟩ with prev_def
  have hprev_val : prev.val = k.val - 1 := rfl
  -- The boundary triple at p = (left p, p, right p).
  -- None of these fire at step prev, so configs are preserved from prev to k.
  -- configVal_eq_of_noFire_between with the 1-step interval [k-1, k).
  have hab : prev.val ≤ k.val := by omega
  have hj_eq : ∀ j : Fin gc.configs.length,
      prev.val ≤ j.val → j.val < k.val → j = prev :=
    fun j hj1 hj2 => Fin.ext (show j.val = prev.val from by omega)
  have hL_eq := configVal_eq_of_noFire_between gc (left p)
      prev.val k.val hab k.isLt
      (fun j hj1 hj2 => by rw [hj_eq j hj1 hj2]; exact hprev_L)
  have hS_eq := configVal_eq_of_noFire_between gc p
      prev.val k.val hab k.isLt
      (fun j hj1 hj2 => by rw [hj_eq j hj1 hj2]; exact hprev_S)
  have hR_eq := configVal_eq_of_noFire_between gc (right p)
      prev.val k.val hab k.isLt
      (fun j hj1 hj2 => by rw [hj_eq j hj1 hj2]; exact hprev_R)
  exact ⟨k, prev, p, hk_mover, hprev_S, hL_eq.symm, hS_eq.symm, hR_eq.symm⟩

/-- Sparse phase argument: under ¬hasEntryConflict, the residual branches
    (tight-odd-left, tight-odd-right, fully contaminated) yield False.
    Replaces the former DominoesRing-based dispatch. -/
private theorem sparse_phase_false
    (gc : GoodCycle sys) (_hn : sys.rs.n ≥ 9)
    (_hsub : subThreshold sys.rs) (_h3bin : hasGe3Binary sys.rs)
    (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (_hmt : sys.rs.m t ≥ 3)
    (hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0)
    (hfc2 : gc.fireCount t ≥ 2)
    (hfc_lt : gc.fireCount t < gc.configs.length)
    (hall_normal : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hnoEC : ¬hasEntryConflict gc) :
    False := by
  -- Step 1: Both binary neighbors fire ≥ 2 times
  have hfc_lt_ge2 : gc.fireCount (left t) ≥ 2 :=
    fireCount_ge_2_of_pos gc (left t) (hfull (left t))
  have hfc_rt_ge2 : gc.fireCount (right t) ≥ 2 :=
    fireCount_ge_2_of_pos gc (right t) (hfull (right t))
  -- Step 2: Under ¬EC, each t-phase has at most 1 first-neighbor fire,
  -- so total first-neighbor fires ≤ number of phases = fireCount(t).
  --
  -- Proof sketch (J+K ≤ 1 per phase under ¬EC):
  --   Under normalForm: (J≥2,K=0) and (J=0,K≥2) are mechanism-triggering,
  --   so J+K ≥ 2 implies J ≥ 1 AND K ≥ 1 (mixed phase).
  --   In a mixed phase, the first non-tight neighbor fire at position q
  --   (q = left t or right t) sees an identical boundary triple at step a+1
  --   (non-mover) and step f_q (mover), PROVIDED the second-neighbor
  --   (left²t or right²t respectively) doesn't fire in between.
  --   For n ≥ 9, second-neighbors are far from t, so the main gap is:
  --   proving second-neighbor silence within the phase (requires the
  --   "contaminated" analysis from the layer-5 infrastructure).
  --   If second-neighbors DO fire: the one-sided suffix
  --   (mixed_normal_has_one_sided_suffix) reduces to tight-odd, which
  --   requires cross-phase boundary-triple chaining ("domino argument").
  -- SORRY: fire-count sparsity bound fc(L) + fc(R) ≤ fc(t).
  -- Proof plan: total L-fires across all phases = fc(L), total R-fires = fc(R),
  -- number of phases = fc(t). If fc(L)+fc(R) > fc(t), pigeonhole gives a phase
  -- with J+K ≥ 2. Case split:
  --   (J≥2, K=0): ec_caseA (parity-chosen L-fire pair, even parity, no LL/t)
  --   (J=0, K≥2): ec_caseB (symmetric)
  --   (J≥1, K≥1): ec_caseC_LR or ec_caseC_RL (cross-neighbor pair)
  -- All three produce hasEntryConflict, contradicting hnoEC.
  -- Requires: fire-count decomposition lemma (sum of intervalFireCount over
  -- phases = fireCount) and phase-level pigeonhole. These are not yet built
  -- in PhaseExtractionBase.
  have h_sparse : gc.fireCount (left t) + gc.fireCount (right t) ≤ gc.fireCount t := by
    -- Proof by contradiction: assume fc(L) + fc(R) > fc(t).
    -- Then pigeonhole gives a phase with J+K ≥ 2, which produces EC.
    by_contra h_gt
    push_neg at h_gt
    -- Per-phase bound: under ¬EC, each phase has J+K ≤ 1.
    -- For any TernaryPhase: if J+K ≥ 2, case split on (J≥2,K=0), (J=0,K≥2),
    -- or (J≥1,K≥1). Each produces hasEntryConflict via ec_caseA/B/C helpers.
    have h_phase_le1 : ∀ phase : TernaryPhase gc t,
        (gc.moverAt phase.a = left t ∨ gc.moverAt phase.a = right t) →
        gc.intervalFireCount (left t) phase.a.val phase.s.val +
        gc.intervalFireCount (right t) phase.a.val phase.s.val ≤ 1 := by
      intro phase ha_adj
      set J := gc.intervalFireCount (left t) phase.a.val phase.s.val
      set K := gc.intervalFireCount (right t) phase.a.val phase.s.val
      have hnorm := hall_normal phase
      have hconstraint := normalForm_gap_constraint gc t phase hnorm
      by_contra h_gt; push_neg at h_gt
      -- J=0 → K=1 (contradicts J+K ≥ 2)
      by_cases hJ0 : J = 0
      · have : K = 1 := hconstraint.1 hJ0; omega
      -- K=0 → J=1 (contradicts J+K ≥ 2)
      by_cases hK0 : K = 0
      · have : J = 1 := hconstraint.2.1 hK0; omega
      -- Mixed case: J ≥ 1 and K ≥ 1. Produce hasEntryConflict gc.
      -- Get first L-fire and first R-fire in [a, s).
      have hJp : J ≥ 1 := Nat.pos_of_ne_zero hJ0
      have hKp : K ≥ 1 := Nat.pos_of_ne_zero hK0
      obtain ⟨fL, hfLa, hfLs, hfLm, hfL_first⟩ :=
        exists_first_fire gc (left t) phase.a.val phase.s.val
          (exists_fire_step_in_interval gc (left t)
            (Nat.le_of_lt phase.ha_lt_s) (Nat.le_of_lt phase.s.isLt) hJp)
      obtain ⟨fR, hfRa, hfRs, hfRm, hfR_first⟩ :=
        exists_first_fire gc (right t) phase.a.val phase.s.val
          (exists_fire_step_in_interval gc (right t)
            (Nat.le_of_lt phase.ha_lt_s) (Nat.le_of_lt phase.s.isLt) hKp)
      have hLR_ne : left t ≠ right t := left_ne_right (by omega : sys.rs.n ≥ 8) t
      have hfne : fL.val ≠ fR.val := fun h =>
        hLR_ne (hfLm ▸ hfRm ▸ congrArg gc.moverAt (Fin.ext h))
      -- Helper: EC at left t between fL (mover) and some step v (non-mover),
      -- given no LL, L, t in [v, fL).
      have mk_ec_left (v : Fin gc.configs.length)
          (hv_lt : v.val < fL.val) (hv_ge : phase.a.val ≤ v.val)
          (hv_noLL : ∀ j : Fin gc.configs.length,
            v.val ≤ j.val → j.val < fL.val → gc.moverAt j ≠ left (left t))
          : hasEntryConflict gc :=
        ⟨fL, v, left t, hfLm,
          fun h => absurd h (hfL_first v hv_ge hv_lt),
          (configVal_eq_of_noFire_between gc (left (left t))
            v.val fL.val (Nat.le_of_lt hv_lt) fL.isLt hv_noLL).symm,
          (configVal_eq_of_noFire_between gc (left t)
            v.val fL.val (Nat.le_of_lt hv_lt) fL.isLt
            (fun j hj1 hj2 => hfL_first j (le_trans hv_ge hj1) hj2)).symm,
          (configVal_eq_of_noFire_between gc (right (left t))
            v.val fL.val (Nat.le_of_lt hv_lt) fL.isLt
            (fun j hj1 hj2 => by
              rw [right_left_eq_self]
              exact phase.ht_nofire j (le_trans hv_ge hj1)
                (lt_trans hj2 hfLs))).symm⟩
      -- Helper: EC at right t between fR (mover) and some step v (non-mover),
      -- given no t, R, RR in [v, fR).
      have mk_ec_right (v : Fin gc.configs.length)
          (hv_lt : v.val < fR.val) (hv_ge : phase.a.val ≤ v.val)
          (hv_noRR : ∀ j : Fin gc.configs.length,
            v.val ≤ j.val → j.val < fR.val → gc.moverAt j ≠ right (right t))
          : hasEntryConflict gc :=
        ⟨fR, v, right t, hfRm,
          fun h => absurd h (hfR_first v hv_ge hv_lt),
          (configVal_eq_of_noFire_between gc (left (right t))
            v.val fR.val (Nat.le_of_lt hv_lt) fR.isLt
            (fun j hj1 hj2 => by
              rw [left_right_eq_self]
              exact phase.ht_nofire j (le_trans hv_ge hj1)
                (lt_trans hj2 hfRs))).symm,
          (configVal_eq_of_noFire_between gc (right t)
            v.val fR.val (Nat.le_of_lt hv_lt) fR.isLt
            (fun j hj1 hj2 => hfR_first j (le_trans hv_ge hj1) hj2)).symm,
          (configVal_eq_of_noFire_between gc (right (right t))
            v.val fR.val (Nat.le_of_lt hv_lt) fR.isLt hv_noRR).symm⟩
      -- Try EC at left t: need a step v < fL with no LL in [v, fL).
      -- v = phase.a works if fL > a and no LL in [a, fL).
      -- Failing that, try EC at right t with v < fR and no RR in [v, fR).
      -- First try: EC at left t using phase.a if fL > a.
      by_cases hfL_gt : phase.a.val < fL.val
      · by_cases hnoLL_aL :
            ∀ j : Fin gc.configs.length,
              phase.a.val ≤ j.val → j.val < fL.val → gc.moverAt j ≠ left (left t)
        · exact hnoEC (mk_ec_left phase.a hfL_gt le_rfl hnoLL_aL)
        · -- LL fires in [a, fL). Find step after last LL → EC at left t.
          push_neg at hnoLL_aL
          obtain ⟨w, hw1, hw2, hwm⟩ := hnoLL_aL
          obtain ⟨wmax, hwma, hwms, hwmm, hwm_last⟩ :=
            exists_last_fire gc (left (left t)) phase.a.val fL.val
              ⟨w, hw1, hw2, hwm⟩
          -- If wmax + 1 < fL: use wmax + 1 as non-mover.
          by_cases hgap : wmax.val + 1 < fL.val
          · have hlt : wmax.val + 1 < gc.configs.length := by omega
            exact hnoEC (mk_ec_left ⟨wmax.val + 1, hlt⟩ (by simp; omega) (by simp; omega)
              (fun j hj1 hj2 => hwm_last j (by simp at hj1; omega) hj2))
          · -- wmax + 1 ≥ fL, i.e., wmax = fL - 1. LL adjacent to first L.
            -- Fall through to EC at right t.
            by_cases hfR_gt : phase.a.val < fR.val
            · by_cases hnoRR_aR :
                  ∀ j : Fin gc.configs.length,
                    phase.a.val ≤ j.val → j.val < fR.val → gc.moverAt j ≠ right (right t)
              · exact hnoEC (mk_ec_right phase.a hfR_gt le_rfl hnoRR_aR)
              · push_neg at hnoRR_aR
                obtain ⟨w2, hw2a, hw2s, hw2m⟩ := hnoRR_aR
                obtain ⟨wmax2, hwm2a, hwm2s, hwm2m, hwm2_last⟩ :=
                  exists_last_fire gc (right (right t)) phase.a.val fR.val
                    ⟨w2, hw2a, hw2s, hw2m⟩
                by_cases hgap2 : wmax2.val + 1 < fR.val
                · have hlt2 : wmax2.val + 1 < gc.configs.length := by omega
                  exact hnoEC (mk_ec_right ⟨wmax2.val + 1, hlt2⟩ (by simp; omega) (by simp; omega)
                    (fun j hj1 hj2 => hwm2_last j (by simp at hj1; omega) hj2))
                · -- Both LL and RR adjacent to first fires.
                  -- wmax = fL - 1 fires LL, wmax2 = fR - 1 fires RR.
                  -- ec_caseC_LR/RL cannot work because second-neighbor fires
                  -- in the interval. Need gap1_ec at the second-neighbor
                  -- plus a chain-of-adjacent-movers induction (not yet built).
                  -- gap1_ec at RR (step wmax2) checks moverAt(wmax2-1):
                  --   ≠ R (fR is first R), so only {RR, right³t} are problematic.
                  --   For the non-adjacent case, gap1_ec gives EC immediately.
                  --   The adjacent sub-case requires deeper backward scanning.
                  -- Vacuous: both fL > a and fR > a, but ha_adj says moverAt(a) = L or R.
                  -- If moverAt(a) = L: contradicts fL being FIRST L-fire after a.
                  -- If moverAt(a) = R: contradicts fR being FIRST R-fire after a.
                  exfalso
                  rcases ha_adj with hadj_L | hadj_R
                  · exact absurd hadj_L (hfL_first phase.a le_rfl hfL_gt)
                  · exact absurd hadj_R (hfR_first phase.a le_rfl hfR_gt)
            · -- fR = a. Use EC at right t with fR = a as mover.
              -- moverAt a = right t. Between a and fL: no R (first R = a = fR,
              -- but fL > a, so between a+1 and fL: no R since fR = a already
              -- fired). Actually fR = a, so fR first fires at a.
              -- ec_caseC_RL between fR and fL? fR < fL.
              -- Between fR and fL: no t (phase), no L (first L at fL), no LL?
              have hfReq : fR.val = phase.a.val := by omega
              -- fR < fL since fR = a < fL
              have hfRL : fR.val < fL.val := by omega
              by_cases hnoLL3 :
                  ∀ k : Fin gc.configs.length,
                    fR.val ≤ k.val → k.val < fL.val → gc.moverAt k ≠ left (left t)
              · exact hnoEC (ec_caseC_RL gc t fR fL hfRm hfLm hfRL
                  (fun k hk1 hk2 =>
                    phase.ht_nofire k (by omega) (lt_trans hk2 hfLs))
                  (fun k hk1 hk2 hkL =>
                    absurd hkL (hfL_first k (by omega) hk2))
                  hnoLL3)
              · -- LL in [fR, fL). Use mk_ec_left with gap after last LL.
                push_neg at hnoLL3
                obtain ⟨w3, hw3a, hw3s, hw3m⟩ := hnoLL3
                obtain ⟨wmax3, hwm3a, hwm3s, hwm3m, hwm3_last⟩ :=
                  exists_last_fire gc (left (left t)) fR.val fL.val
                    ⟨w3, hw3a, hw3s, hw3m⟩
                by_cases hgap3 : wmax3.val + 1 < fL.val
                · have hlt3 : wmax3.val + 1 < gc.configs.length := by omega
                  exact hnoEC (mk_ec_left ⟨wmax3.val + 1, hlt3⟩ (by simp; omega) (by simp; omega)
                    (fun j hj1 hj2 => hwm3_last j (by simp at hj1; omega) hj2))
                · -- LL adjacent to fL, with fR = a.
                  -- wmax3 = fL - 1. Find FIRST LL fire in [a, fL).
                  -- EC at LL between first-LL (mover) and a (non-mover).
                  obtain ⟨fLL, hfLLa, hfLLb, hfLLm, hfLL_first⟩ :=
                    exists_first_fire gc (left (left t)) fR.val fL.val
                      ⟨w3, hw3a, hw3s, hw3m⟩
                  -- moverAt(a) = R ≠ LL
                  have ha_ne_LL : gc.moverAt phase.a ≠ left (left t) := by
                    rw [show (phase.a : Fin gc.configs.length) = fR from Fin.ext (by omega)]
                    rw [hfRm]
                    exact (left2_ne_right (by omega : sys.rs.n ≥ 8) t).symm
                  -- Need: no left³t, LL, L fire in [a, fLL).
                  -- No LL: first is fLL. No L: first L is fL > fLL.
                  -- left³t: case split.
                  by_cases hnoL3 :
                      ∀ j : Fin gc.configs.length,
                        fR.val ≤ j.val → j.val < fLL.val →
                        gc.moverAt j ≠ left (left (left t))
                  · -- No left³t in [a, fLL). EC at LL.
                    have hrlleq : right (left (left t)) = left t := right_left_eq_self (left t)
                    exact hnoEC ⟨fLL, phase.a, left (left t), hfLLm,
                      (by rw [show (phase.a : Fin gc.configs.length) = fR from Fin.ext (by omega)]
                          rw [hfRm]; exact (left2_ne_right (by omega : sys.rs.n ≥ 8) t).symm),
                      (configVal_eq_of_noFire_between gc (left (left (left t)))
                        phase.a.val fLL.val (by omega) fLL.isLt
                        (fun j hj1 hj2 => hnoL3 j (by omega) hj2)).symm,
                      (configVal_eq_of_noFire_between gc (left (left t))
                        phase.a.val fLL.val (by omega) fLL.isLt
                        (fun j hj1 hj2 => hfLL_first j (by omega) hj2)).symm,
                      (by rw [hrlleq]
                          exact (configVal_eq_of_noFire_between gc (left t)
                            phase.a.val fLL.val (by omega) fLL.isLt
                            (fun j hj1 hj2 => hfL_first j (by omega)
                              (lt_trans hj2 hfLLb))).symm)⟩
                  · -- left³t fires in [a, fLL). Adjacent-chain continues.
                    -- Needs backward-scanning induction (not yet built).
                    exact absurd (show hasEntryConflict gc from by sorry) hnoEC
      · -- fL = a. Symmetric: try EC at right t.
        have hfLeq : fL.val = phase.a.val := by omega
        -- fR > a (since fL = a and fL ≠ fR)
        have hfR_gt2 : phase.a.val < fR.val := by omega
        by_cases hnoRR_aR2 :
            ∀ j : Fin gc.configs.length,
              phase.a.val ≤ j.val → j.val < fR.val → gc.moverAt j ≠ right (right t)
        · exact hnoEC (mk_ec_right phase.a hfR_gt2 le_rfl hnoRR_aR2)
        · push_neg at hnoRR_aR2
          obtain ⟨w4, hw4a, hw4s, hw4m⟩ := hnoRR_aR2
          obtain ⟨wmax4, hwm4a, hwm4s, hwm4m, hwm4_last⟩ :=
            exists_last_fire gc (right (right t)) phase.a.val fR.val
              ⟨w4, hw4a, hw4s, hw4m⟩
          by_cases hgap4 : wmax4.val + 1 < fR.val
          · have hlt4 : wmax4.val + 1 < gc.configs.length := by omega
            exact hnoEC (mk_ec_right ⟨wmax4.val + 1, hlt4⟩ (by simp; omega) (by simp; omega)
              (fun j hj1 hj2 => hwm4_last j (by simp at hj1; omega) hj2))
          · -- RR adjacent to fR, fL = a.
            -- wmax4 = fR-1 fires RR. Find FIRST RR fire in [a, fR).
            obtain ⟨fRR, hfRRa, hfRRb, hfRRm, hfRR_first⟩ :=
              exists_first_fire gc (right (right t)) phase.a.val fR.val
                ⟨w4, hw4a, hw4s, hw4m⟩
            -- moverAt(a) = L ≠ RR
            have hlrreq : left (right (right t)) = right t := left_right_eq_self (right t)
            by_cases hnoR3 :
                ∀ j : Fin gc.configs.length,
                  phase.a.val ≤ j.val → j.val < fRR.val →
                  gc.moverAt j ≠ right (right (right t))
            · -- No right³t in [a, fRR). EC at RR.
              exact hnoEC ⟨fRR, phase.a, right (right t), hfRRm,
                (by rw [show (phase.a : Fin gc.configs.length) = fL from Fin.ext (by omega)]
                    rw [hfLm]; exact (right2_ne_left (by omega : sys.rs.n ≥ 8) t).symm),
                (by rw [hlrreq]
                    exact (configVal_eq_of_noFire_between gc (right t)
                      phase.a.val fRR.val (by omega) fRR.isLt
                      (fun j hj1 hj2 => hfR_first j (by omega)
                        (lt_trans hj2 hfRRb))).symm),
                (configVal_eq_of_noFire_between gc (right (right t))
                  phase.a.val fRR.val (by omega) fRR.isLt
                  (fun j hj1 hj2 => hfRR_first j (by omega) hj2)).symm,
                (configVal_eq_of_noFire_between gc (right (right (right t)))
                  phase.a.val fRR.val (by omega) fRR.isLt hnoR3).symm⟩
            · -- right³t fires in [a, fRR). Adjacent-chain continues.
              exact absurd (show hasEntryConflict gc from by sorry) hnoEC
    -- Summation: h_phase_le1 (J+K ≤ 1 per phase) → fc(L)+fc(R) ≤ fc(t).
    -- Requires fire-count decomposition: every L-fire and R-fire falls in
    -- exactly one phase (between consecutive t-fires), so
    --   fc(L) = Σ_phases J_i, fc(R) = Σ_phases K_i.
    -- Then fc(L)+fc(R) = Σ (J_i+K_i) ≤ Σ 1 = fc(t).
    -- This decomposition is not yet in PhaseExtractionBase.
    have h_le : gc.fireCount (left t) + gc.fireCount (right t) ≤ gc.fireCount t := by
      -- Convert h_phase_le1 to the form needed by ifc_sum_le_of_consec_le1:
      -- every consecutive t-pair (a,s) has ifc(L,a,s) + ifc(R,a,s) ≤ 1.
      have hall_le1 : ∀ (a s : Fin gc.configs.length),
          a.val < s.val → gc.moverAt a = t → gc.moverAt s = t →
          (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
          gc.intervalFireCount (left t) a.val s.val +
            gc.intervalFireCount (right t) a.val s.val ≤ 1 := by
        intro a s has ha hs hno
        -- Step a fires t ≠ left t, right t, so single-step ifc = 0.
        have hstepL : gc.intervalFireCount (left t) a.val (a.val + 1) = 0 := by
          rw [intervalFireCount_single_eq gc (left t) a.val a.isLt]
          simp [show gc.moverAt a ≠ left t from by
            rw [ha]; intro h; have hval := congrArg Fin.val h
            simp only [left_val] at hval
            have hn := sys.rs.n_ge_4; have ht := t.isLt
            by_cases h0 : t.val = 0
            · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hval; omega
            · rw [show t.val + sys.rs.n - 1 = (t.val - 1) + sys.rs.n from by omega,
                  Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hval; omega]
        have hstepR : gc.intervalFireCount (right t) a.val (a.val + 1) = 0 := by
          rw [intervalFireCount_single_eq gc (right t) a.val a.isLt]
          simp [show gc.moverAt a ≠ right t from by
            rw [ha]; intro h; have hval := congrArg Fin.val h
            simp only [right, Fin.val_mk] at hval
            have hn := sys.rs.n_ge_4; have ht := t.isLt
            by_cases hlast : t.val + 1 = sys.rs.n
            · rw [hlast, Nat.mod_self] at hval; omega
            · rw [Nat.mod_eq_of_lt (by omega)] at hval; omega]
        by_cases hgap : a.val + 1 < s.val
        · -- Non-empty gap: construct TernaryPhase, use h_phase_le1
          have ha1_lt : a.val + 1 < gc.configs.length := by omega
          let a1 : Fin gc.configs.length := ⟨a.val + 1, ha1_lt⟩
          have ha1_ne : gc.moverAt a1 ≠ t :=
            hno a1 (by show a.val < a1.val; simp [a1]) (by show a1.val < s.val; omega)
          have ha1_nofire : ∀ k : Fin gc.configs.length,
              a1.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ t :=
            fun k hk1 hk2 => hno k (by simp [a1] at hk1; omega) hk2
          let phase : TernaryPhase gc t :=
            { a := a1, s := s, ha_lt_s := hgap, hs_mover := hs,
              ha_nonmover := ha1_ne, ht_nofire := ha1_nofire }
          have ha_adj : gc.moverAt a1 = left t ∨ gc.moverAt a1 = right t := by
            have hlocal := gc.next_mover_is_local a
            have hnext_eq : nextIndex gc.configs a = a1 := by
              ext; simp [nextIndex, a1, Nat.mod_eq_of_lt (by omega : a.val + 1 < gc.configs.length)]
            rw [ha] at hlocal; rw [hnext_eq] at hlocal
            rcases hlocal with h | h | h
            · exact Or.inl h
            · exact absurd h ha1_ne
            · exact Or.inr h
          have hle := h_phase_le1 phase ha_adj
          -- phase.a = a1, phase.s = s, so phase J/K = ifc on [a+1, s)
          have hpa : phase.a.val = a.val + 1 := rfl
          have hps : phase.s.val = s.val := rfl
          -- Split: ifc(p, a, s) = ifc(p, a, a+1) + ifc(p, a+1, s)
          have hsplitL := intervalFireCount_split gc (left t)
            (show a.val ≤ a.val + 1 by omega) (show a.val + 1 ≤ s.val by omega)
          have hsplitR := intervalFireCount_split gc (right t)
            (show a.val ≤ a.val + 1 by omega) (show a.val + 1 ≤ s.val by omega)
          -- ifc on [a, s) = 0 + ifc on [a+1, s) = phase J + phase K
          rw [hpa, hps] at hle
          omega
        · -- Empty gap: a+1 ≥ s, so a+1 = s (from has).
          have heq : a.val + 1 = s.val := by omega
          -- ifc on [a, s) = ifc on [a, a+1) = 0 for both L and R
          have hsplitL := intervalFireCount_split gc (left t)
            (show a.val ≤ a.val + 1 by omega) (show a.val + 1 ≤ s.val by omega)
          have hsplitR := intervalFireCount_split gc (right t)
            (show a.val ≤ a.val + 1 by omega) (show a.val + 1 ≤ s.val by omega)
          have htailL : gc.intervalFireCount (left t) (a.val + 1) s.val = 0 := by
            rw [heq]; simp [GoodCycle.intervalFireCount]
          have htailR : gc.intervalFireCount (right t) (a.val + 1) s.val = 0 := by
            rw [heq]; simp [GoodCycle.intervalFireCount]
          omega
      -- Use intervalFireCount_add_phases to bound total.
      -- Strategy: interior ≤ fc(t)-1 from ifc_sum_le_of_consec_le1,
      -- wrap ≤ 1 from constructing a TernaryPhase for the cyclic gap.
      -- Total ≤ fc(t).
      -- For now, this requires the full min/max + wrap infrastructure.
      -- Since we already have h_phase_le1 (each TernaryPhase has J+K ≤ 1)
      -- and hall_le1 (each consecutive pair has sum ≤ 1), the bound follows
      -- from the cyclic decomposition: fc(t) consecutive pairs, each ≤ 1.
      sorry
    omega
  -- Step 3: fireCount(t) ≥ 4, pigeonhole gives a free phase → EC
  have hfc_ge4 : gc.fireCount t ≥ 4 := by omega
  -- Binary neighbors fire an even number of times
  have hfc_lt_even : Even (gc.fireCount (left t)) :=
    gc.binary_fireCount_even (left t) hbL
  have hfc_rt_even : Even (gc.fireCount (right t)) :=
    gc.binary_fireCount_even (right t) hbR
  -- Step 4: derive EC from h_sparse + fc(t) ≥ 4.
  -- With sparse_phase_sum_ge (PhaseExtractionBase): fc(L)+fc(R) ≥ fc(t).
  -- Combined with h_sparse: fc(L)+fc(R) = fc(t), each phase has J+K = 1.
  -- From h_sparse: fc(R) ≤ fc(t) - 2 < fc(t), so
  -- exists_consecutive_tfire_with_zero_qfire (PhaseExtractionBase) gives a
  -- phase with K = 0, hence J = 1 (normalForm). This is a one-sided-left
  -- phase with a single tight fire. intervalFireCount(left t, a1, s) = 1
  -- (odd), so tight_even_left_ec doesn't apply.
  --
  -- The tight-odd one-sided phase requires a cross-phase chaining argument:
  -- the boundary triple at left t propagates across consecutive phases
  -- (each with J+K = 1), and the binary parity constraint forces a full
  -- cycle around the ring → EC. This "domino" argument is the remaining
  -- hard step (requires phase-sum decomposition + ring topology).
  -- h_sparse gives fc(L)+fc(R) ≤ fc(t).
  -- sparse_phase_sum_ge gives fc(L)+fc(R) ≥ fc(t) (under ¬EC + normalForm).
  -- So fc(L)+fc(R) = fc(t), meaning each phase has J+K = 1.
  -- Pigeonhole (fc(R) ≤ fc(t)-2 < fc(t)) gives a phase with K=0, J=1.
  -- That one-sided tight-odd phase produces EC via cross-phase chaining.
  -- Consecutive t-fires are excluded: under hall_normal + hnoEC + binary neighbors,
  -- the per-phase normalForm constraint on adjacent phases forces non-empty gaps.
  -- (bothEvenReturn_ec dispatches any phase with even L+R counts; the adjacent
  -- phase parity chain forces a mechanism-triggering gap somewhere.)
  have hno_consec : ∀ (a s : Fin gc.configs.length),
      a.val < s.val → gc.moverAt a = t → gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      a.val + 1 < s.val := by
    sorry
  have hno_cyclic_consec : ∀ k : Fin gc.configs.length, gc.moverAt k = t →
      gc.moverAt ⟨(k.val + 1) % gc.configs.length,
        Nat.mod_lt _ gc.configs_length_pos⟩ ≠ t := by
    sorry
  have h_ge := sparse_phase_sum_ge gc t hbL hbR hfc2 hfc_lt hall_normal hnoEC hno_consec
    hno_cyclic_consec
  -- fc(L)+fc(R) = fc(t)
  have h_eq : gc.fireCount (left t) + gc.fireCount (right t) = gc.fireCount t := by omega
  -- SORRY: derive EC from exact-equality fc(L)+fc(R) = fc(t).
  -- With h_eq: each phase has exactly J+K = 1. Pigeonhole on fc(R) ≤ fc(t)-2
  -- (since fc(R) ≥ 2 and fc(L) ≥ 2, so fc(R) = fc(t) - fc(L) ≤ fc(t) - 2)
  -- gives a phase with K = 0, hence J = 1 (one-sided-left, tight).
  -- intervalFireCount(L, a1, s) = 1 (odd), so tight_even_left_ec does NOT apply.
  -- The tight-odd one-sided phase requires a cross-phase chaining ("domino")
  -- argument: boundary triple at left t propagates across consecutive phases,
  -- and binary parity constraint forces a full cycle around the ring → EC.
  -- This domino argument needs: (1) phase adjacency structure (consecutive
  -- phases share a t-fire step), (2) cross-phase config propagation lemmas,
  -- (3) binary half-cycle overlap from the ring topology.
  -- These are not yet built.
  have h_ec : hasEntryConflict gc := by sorry
  exact absurd h_ec hnoEC

/-! ### Main theorem -/

set_option maxHeartbeats 1000000 in
theorem allNormalForm_false2
    (gc : GoodCycle sys) (_hn : sys.rs.n ≥ 9)
    (_hconv : converges sys gc)
    (_hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (_hsub : subThreshold sys.rs) (_h3bin : hasGe3Binary sys.rs)
    (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (hmt : sys.rs.m t ≥ 3)
    (hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0)
    (hfc2 : gc.fireCount t ≥ 2)
    (hfc_lt : gc.fireCount t < gc.configs.length)
    (hall_normal : ∀ phase : TernaryPhase gc t,
      isNormalFormGap gc t phase) :
    False := by
  -- Strategy: find a "good phase" (non-tight, free second-neighbor, active
  -- first-neighbor) and apply within-phase EC. If no good phase exists,
  -- fall through to layers 3-6 (hard case).
  by_contra h_not_false
  -- For each phase, the non-tight EC at left t or right t would give False.
  -- So if False doesn't hold, no phase is "good" in the non-tight sense.
  -- Derive: every phase is either tight or has no free second-neighbor.
  -- This is the condition for layers 3-6.
  have h_no_nontight_ec : ∀ (phase : TernaryPhase gc t)
      (f : Fin gc.configs.length),
      phase.a.val < f.val → f.val < phase.s.val →
      gc.moverAt f = left t →
      (∀ k : Fin gc.configs.length,
        phase.a.val < k.val → k.val < f.val → gc.moverAt k ≠ left t) →
      (∀ k : Fin gc.configs.length,
        phase.a.val < k.val → k.val < phase.s.val →
        gc.moverAt k ≠ left (left t)) →
      f.val ≤ phase.a.val + 1 := by
    intro phase f hf1 hf2 hfm hff hnl2
    by_contra hgap
    push_neg at hgap
    exact h_not_false (within_phase_ec_left gc t phase f ⟨hf1, hf2⟩ hfm hff hnl2 hgap)
  -- Symmetric for right side
  have h_no_nontight_ec_right : ∀ (phase : TernaryPhase gc t)
      (f : Fin gc.configs.length),
      phase.a.val < f.val → f.val < phase.s.val →
      gc.moverAt f = right t →
      (∀ k : Fin gc.configs.length,
        phase.a.val < k.val → k.val < f.val → gc.moverAt k ≠ right t) →
      (∀ k : Fin gc.configs.length,
        phase.a.val < k.val → k.val < phase.s.val →
        gc.moverAt k ≠ right (right t)) →
      f.val ≤ phase.a.val + 1 := by
    intro phase f hf1 hf2 hfm hff hnr2
    by_contra hgap
    push_neg at hgap
    exact h_not_false (within_phase_ec_right gc t phase f ⟨hf1, hf2⟩ hfm hff hnr2 hgap)
  -- Step 1: if a second-neighbor stays silent and the corresponding
  -- first-neighbor fires strictly inside the phase, then that firing is tight:
  -- it occurs at `phase.a + 1`.
  have h_left_free_tight : ∀ (phase : TernaryPhase gc t),
      (∀ k : Fin gc.configs.length,
        phase.a.val < k.val → k.val < phase.s.val →
        gc.moverAt k ≠ left (left t)) →
      (∃ f : Fin gc.configs.length,
        phase.a.val < f.val ∧ f.val < phase.s.val ∧ gc.moverAt f = left t) →
      ∃ a1 : Fin gc.configs.length,
        a1.val = phase.a.val + 1 ∧ gc.moverAt a1 = left t := by
    intro phase hno_left2 hleft
    obtain ⟨f, hf1, hf2, hfm, hfirst⟩ :=
      exists_first_strict_fire gc (left t) phase.a.val phase.s.val hleft
    have hf_le : f.val ≤ phase.a.val + 1 :=
      h_no_nontight_ec phase f hf1 hf2 hfm hfirst hno_left2
    have ha1_lt : phase.a.val + 1 < gc.configs.length := by
      have := phase.ha_lt_s
      have := phase.s.isLt
      omega
    let a1 : Fin gc.configs.length := ⟨phase.a.val + 1, ha1_lt⟩
    have hf_eq : f = a1 := by
      apply Fin.ext
      dsimp [a1]
      omega
    refine ⟨a1, rfl, ?_⟩
    simpa [hf_eq] using hfm
  have h_right_free_tight : ∀ (phase : TernaryPhase gc t),
      (∀ k : Fin gc.configs.length,
        phase.a.val < k.val → k.val < phase.s.val →
        gc.moverAt k ≠ right (right t)) →
      (∃ f : Fin gc.configs.length,
        phase.a.val < f.val ∧ f.val < phase.s.val ∧ gc.moverAt f = right t) →
      ∃ a1 : Fin gc.configs.length,
        a1.val = phase.a.val + 1 ∧ gc.moverAt a1 = right t := by
    intro phase hno_right2 hright
    obtain ⟨f, hf1, hf2, hfm, hfirst⟩ :=
      exists_first_strict_fire gc (right t) phase.a.val phase.s.val hright
    have hf_le : f.val ≤ phase.a.val + 1 :=
      h_no_nontight_ec_right phase f hf1 hf2 hfm hfirst hno_right2
    have ha1_lt : phase.a.val + 1 < gc.configs.length := by
      have := phase.ha_lt_s
      have := phase.s.isLt
      omega
    let a1 : Fin gc.configs.length := ⟨phase.a.val + 1, ha1_lt⟩
    have hf_eq : f = a1 := by
      apply Fin.ext
      dsimp [a1]
      omega
    refine ⟨a1, rfl, ?_⟩
    simpa [hf_eq] using hfm
  -- Step 2: in every normal phase, at least one first-neighbor fires.
  have h_phase_has_neighbor_count : ∀ (phase : TernaryPhase gc t),
      0 < gc.intervalFireCount (left t) phase.a.val phase.s.val ∨
      0 < gc.intervalFireCount (right t) phase.a.val phase.s.val := by
    intro phase
    let J := gc.intervalFireCount (left t) phase.a.val phase.s.val
    let K := gc.intervalFireCount (right t) phase.a.val phase.s.val
    have hnorm : isNormalFormGap gc t phase := hall_normal phase
    have hconstraint := normalForm_gap_constraint gc t phase hnorm
    by_contra hnone
    push_neg at hnone
    have hJ0 : J = 0 := by omega
    have hK0 : K = 0 := by omega
    have : K = 1 := hconstraint.1 hJ0
    omega
  have h_phase_has_neighbor : ∀ (phase : TernaryPhase gc t),
      gc.moverAt phase.a = left t ∨
      gc.moverAt phase.a = right t ∨
      (∃ f : Fin gc.configs.length,
        phase.a.val < f.val ∧ f.val < phase.s.val ∧ gc.moverAt f = left t) ∨
      (∃ f : Fin gc.configs.length,
        phase.a.val < f.val ∧ f.val < phase.s.val ∧ gc.moverAt f = right t) := by
    intro phase
    rcases h_phase_has_neighbor_count phase with hJ_pos | hK_pos
    · by_cases hstartL : gc.moverAt phase.a = left t
      · exact Or.inl hstartL
      · obtain ⟨f, hfa, hfs, hfm⟩ := exists_fire_step_in_interval gc (left t)
          (Nat.le_of_lt phase.ha_lt_s)
          (Nat.le_of_lt phase.s.isLt)
          (Nat.succ_le_of_lt hJ_pos)
        have hf_gt : phase.a.val < f.val := by
          by_contra hle
          have hf_eq : f = phase.a := by
            apply Fin.ext
            omega
          exact hstartL (by simpa [hf_eq] using hfm)
        exact Or.inr (Or.inr (Or.inl ⟨f, hf_gt, hfs, hfm⟩))
    · by_cases hstartR : gc.moverAt phase.a = right t
      · exact Or.inr (Or.inl hstartR)
      · obtain ⟨f, hfa, hfs, hfm⟩ := exists_fire_step_in_interval gc (right t)
          (Nat.le_of_lt phase.ha_lt_s)
          (Nat.le_of_lt phase.s.isLt)
          (Nat.succ_le_of_lt hK_pos)
        have hf_gt : phase.a.val < f.val := by
          by_contra hle
          have hf_eq : f = phase.a := by
            apply Fin.ext
            omega
          exact hstartR (by simpa [hf_eq] using hfm)
        exact Or.inr (Or.inr (Or.inr ⟨f, hf_gt, hfs, hfm⟩))
  -- Reduced residual: either we already have a tight free-side phase on the
  -- left/right, or else every phase begins with a first-neighbor fire or
  -- contains a second-neighbor fire strictly inside the phase.
  have h_reduced :
      (∃ phase : TernaryPhase gc t,
        (∀ k : Fin gc.configs.length,
          phase.a.val < k.val → k.val < phase.s.val →
          gc.moverAt k ≠ left (left t)) ∧
        ∃ a1 : Fin gc.configs.length,
          a1.val = phase.a.val + 1 ∧ gc.moverAt a1 = left t) ∨
      (∃ phase : TernaryPhase gc t,
        (∀ k : Fin gc.configs.length,
          phase.a.val < k.val → k.val < phase.s.val →
          gc.moverAt k ≠ right (right t)) ∧
        ∃ a1 : Fin gc.configs.length,
          a1.val = phase.a.val + 1 ∧ gc.moverAt a1 = right t) ∨
      (∀ phase : TernaryPhase gc t,
        gc.moverAt phase.a = left t ∨
        gc.moverAt phase.a = right t ∨
        ∃ k : Fin gc.configs.length,
          phase.a.val < k.val ∧ k.val < phase.s.val ∧
          (gc.moverAt k = left (left t) ∨ gc.moverAt k = right (right t))) := by
    by_cases hfreeL : ∃ phase : TernaryPhase gc t,
        (∀ k : Fin gc.configs.length,
          phase.a.val < k.val → k.val < phase.s.val →
          gc.moverAt k ≠ left (left t)) ∧
        (∃ f : Fin gc.configs.length,
          phase.a.val < f.val ∧ f.val < phase.s.val ∧ gc.moverAt f = left t)
    · rcases hfreeL with ⟨phase, hno_left2, hleft⟩
      exact Or.inl ⟨phase, hno_left2, h_left_free_tight phase hno_left2 hleft⟩
    · by_cases hfreeR : ∃ phase : TernaryPhase gc t,
          (∀ k : Fin gc.configs.length,
            phase.a.val < k.val → k.val < phase.s.val →
            gc.moverAt k ≠ right (right t)) ∧
          (∃ f : Fin gc.configs.length,
            phase.a.val < f.val ∧ f.val < phase.s.val ∧ gc.moverAt f = right t)
      · rcases hfreeR with ⟨phase, hno_right2, hright⟩
        exact Or.inr (Or.inl
          ⟨phase, hno_right2, h_right_free_tight phase hno_right2 hright⟩)
      · refine Or.inr (Or.inr ?_)
        intro phase
        rcases h_phase_has_neighbor phase with hstartL | hstartR | hstrictL | hstrictR
        · exact Or.inl hstartL
        · exact Or.inr (Or.inl hstartR)
        · have hleft2 :
            ∃ k : Fin gc.configs.length,
              phase.a.val < k.val ∧ k.val < phase.s.val ∧
              gc.moverAt k = left (left t) := by
            by_contra hnone
            exact hfreeL ⟨phase,
              (fun k hk1 hk2 hkll => hnone ⟨k, hk1, hk2, hkll⟩),
              hstrictL⟩
          rcases hleft2 with ⟨k, hk1, hk2, hkll⟩
          exact Or.inr (Or.inr ⟨k, hk1, hk2, Or.inl hkll⟩)
        · have hright2 :
            ∃ k : Fin gc.configs.length,
              phase.a.val < k.val ∧ k.val < phase.s.val ∧
              gc.moverAt k = right (right t) := by
            by_contra hnone
            exact hfreeR ⟨phase,
              (fun k hk1 hk2 hkrr => hnone ⟨k, hk1, hk2, hkrr⟩),
              hstrictR⟩
          rcases hright2 with ⟨k, hk1, hk2, hkrr⟩
          exact Or.inr (Or.inr ⟨k, hk1, hk2, Or.inr hkrr⟩)
  -- Remaining hard case:
  --   * either some phase has a free second-neighbor and the corresponding
  --     first-neighbor fires tightly at `phase.a + 1`, or
  --   * every phase starts at `left t` / `right t`, or contains a strict
  --     second-neighbor firing.
  --
  -- Closing this requires the global layers 3-6 infrastructure alluded to in
  -- the statement: cross-pivot parity for tight phases and the binary
  -- half-cycle overlap argument. That would further reduce the residue to the
  -- genuinely hard all-binary / `fireCount t = 2` configuration.
  -- All residual branches (tight-odd-left, tight-odd-right, contaminated) are
  -- closed by the sparse phase argument under ¬EC. We case-split on EC first.
  by_cases hEC : hasEntryConflict gc
  · exact h_not_false (entryConflict_impossible gc hEC)
  · -- Under ¬EC, all three residual branches yield False via sparse phases.
    rcases h_reduced with hleft | hright | hall_contaminated
    · rcases hleft with ⟨phase, hno_left2, a1, ha1, ha1_left⟩
      by_cases h_even : Even (gc.intervalFireCount (left t) a1.val phase.s.val)
      · exact tight_even_left_ec gc t phase hbL hno_left2 a1 ha1 ha1_left h_even
      · exact sparse_phase_false gc _hn _hsub _h3bin t hbL hbR hmt hfull hfc2 hfc_lt hall_normal hEC
    · rcases hright with ⟨phase, hno_right2, a1, ha1, ha1_right⟩
      by_cases h_even : Even (gc.intervalFireCount (right t) a1.val phase.s.val)
      · exact tight_even_right_ec gc t phase hbR hno_right2 a1 ha1 ha1_right h_even
      · exact sparse_phase_false gc _hn _hsub _h3bin t hbL hbR hmt hfull hfc2 hfc_lt hall_normal hEC
    · exact sparse_phase_false gc _hn _hsub _h3bin t hbL hbR hmt hfull hfc2 hfc_lt hall_normal hEC

end LeanMn
