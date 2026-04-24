/-
  NormalFormEC.lean — Cross-phase entry conflict from allNormalForm residual

  Shared component used by ZeroWinding, Sweep, and OddWinding cases.

  Given a sandwiched ternary t (both neighbors binary) where all TernaryPhases
  are in normalForm, derive hasEntryConflict.

  Proof (from lb_complete_proof.md, "allNormalFormFalse2 Argument"):
  1. Non-empty phases have J+K = 1 (one-sided: exactly one binary fires once)
  2. Some one-sided phase has length ≥ 2 (pigeonhole from CL ≥ 2n)
  3. Constant triple at t in the long phase → EC (within_phase_ec)
  4. BFL case: backward EC from adjacent-chain scanning

  Sorry map:
  - `normalForm_sparse_phase_false` — fire-count summation + cross-phase EC
    Maps to: lb_complete_proof.md "The cross-phase EC argument" + "Why a long
    one-sided phase exists"
  - The BFL sub-case (backward chain when left³t or right³t fires adjacent
    to the first-neighbor fire) is the hardest sorry.
-/
import LeanMn.LowerBound.EntryConflict.PhaseExtractionBase
import LeanMn.LowerBound.EntryConflict.ContextBridge
import LeanMn.LowerBound.EntryConflict.BinaryParity

namespace LeanMn

variable {sys : System}

/-! ### Within-phase EC helpers (sorry-free)

If a first-neighbor fires strictly inside a phase and there's a gap between
the t-firing and the first-neighbor firing, the boundary triple at the
first-neighbor is constant → EC. -/

/-- Non-tight within-phase EC at left t.
    Step f is the first left-t fire in the phase, with f > phase.a + 1 and
    no left²t fires in the phase. The triple at left t is constant from
    phase.a+1 to f → EC. -/
private theorem within_phase_ec_left
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (f : Fin gc.configs.length)
    (hf_range : phase.a.val < f.val ∧ f.val < phase.s.val)
    (hf_mover : gc.moverAt f = left t)
    (hf_first : ∀ k : Fin gc.configs.length,
      phase.a.val < k.val → k.val < f.val → gc.moverAt k ≠ left t)
    (h_no_left2 : ∀ k : Fin gc.configs.length,
      phase.a.val < k.val → k.val < phase.s.val →
      gc.moverAt k ≠ left (left t))
    (hf_gap : f.val > phase.a.val + 1) :
    False := by
  have hf_lt_s := hf_range.2
  have hf_gt_a := hf_range.1
  have ha1_lt : phase.a.val + 1 < gc.configs.length := by
    have := phase.ha_lt_s; have := phase.s.isLt; omega
  set a1 : Fin gc.configs.length := ⟨phase.a.val + 1, ha1_lt⟩
  have ha1_val : a1.val = phase.a.val + 1 := rfl
  have ha1_ne : gc.moverAt a1 ≠ left t :=
    hf_first a1 (by simp [a1]) (by simp [a1]; omega)
  have hab : a1.val ≤ f.val := by omega
  have hL_eq := configVal_eq_of_noFire_between gc (left (left t))
      a1.val f.val hab f.isLt
      (fun k hk1 hk2 => h_no_left2 k (by omega) (by omega))
  have hS_eq := configVal_eq_of_noFire_between gc (left t)
      a1.val f.val hab f.isLt
      (fun k hk1 hk2 => hf_first k (by omega) hk2)
  have hrl : right (left t) = t := right_left_eq_self t
  have hR_eq := configVal_eq_of_noFire_between gc (right (left t))
      a1.val f.val hab f.isLt
      (fun k hk1 hk2 => by rw [hrl]; exact phase.ht_nofire k (by omega) (by omega))
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
  have hf_lt_s := hf_range.2
  have hf_gt_a := hf_range.1
  have ha1_lt : phase.a.val + 1 < gc.configs.length := by
    have := phase.ha_lt_s; have := phase.s.isLt; omega
  set a1 : Fin gc.configs.length := ⟨phase.a.val + 1, ha1_lt⟩
  have ha1_val : a1.val = phase.a.val + 1 := rfl
  have ha1_ne : gc.moverAt a1 ≠ right t :=
    hf_first a1 (by simp [a1]) (by simp [a1]; omega)
  have hab : a1.val ≤ f.val := by omega
  have hlr : left (right t) = t := left_right_eq_self t
  have hL_eq := configVal_eq_of_noFire_between gc (left (right t))
      a1.val f.val hab f.isLt
      (fun k hk1 hk2 => by rw [hlr]; exact phase.ht_nofire k (by omega) (by omega))
  have hS_eq := configVal_eq_of_noFire_between gc (right t)
      a1.val f.val hab f.isLt
      (fun k hk1 hk2 => hf_first k (by omega) hk2)
  have hR_eq := configVal_eq_of_noFire_between gc (right (right t))
      a1.val f.val hab f.isLt
      (fun k hk1 hk2 => h_no_right2 k (by omega) (by omega))
  exact entryConflict_impossible gc
    ⟨f, a1, right t, hf_mover, ha1_ne,
      hL_eq.symm, hS_eq.symm, hR_eq.symm⟩

/-! ### Fire selection helpers (sorry-free) -/

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
    intro j hj
    exact Finset.le_max' S j hj
  have hkmax_data : a ≤ kmax.val ∧ kmax.val < b ∧ gc.moverAt kmax = p := by
    simpa [S, kmax] using hkmax_mem
  rcases hkmax_data with ⟨hka, hkb, hkm⟩
  refine ⟨kmax, hka, hkb, hkm, ?_⟩
  intro j hjk hjb hjm
  have hj_mem : j ∈ S := by
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_univ j, ?_⟩
    exact ⟨by omega, hjb, hjm⟩
  have := hkmax_ge j hj_mem
  omega

/-! ### Full-support helpers for the structural route -/

/-- Full support immediately rules out a safe processor: if some processor `q`
    were safe, it would never be the mover, contradicting `fireCount q > 0`. -/
private theorem hno_safe_of_hfull
    (gc : GoodCycle sys)
    (hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0) :
    ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q := by
  intro hsafe
  rcases hsafe with ⟨q, hq⟩
  have hnever : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ q := fun k => (hq k).1
  have : gc.fireCount q = 0 := by
    rw [gc.fireCount_eq_sum_moverAt q]
    apply Finset.sum_eq_zero
    intro k _
    simp [hnever k]
  have hq_pos := hfull q
  omega

/-- When `n ≥ 9`, some processor lies outside the local five-set
    `{left² t, left t, t, right t, right² t}`. -/
private theorem exists_outside_local_five
    (hn : sys.rs.n ≥ 9) (t : Fin sys.rs.n) :
    ∃ p : Fin sys.rs.n,
      p ≠ left (left t) ∧ p ≠ left t ∧ p ≠ t ∧
      p ≠ right t ∧ p ≠ right (right t) := by
  by_contra hall
  push_neg at hall
  have hcover :
      ∀ p : Fin sys.rs.n,
        p = left (left t) ∨ p = left t ∨ p = t ∨
          p = right t ∨ p = right (right t) := by
    intro p
    by_cases hp_ll : p = left (left t)
    · exact Or.inl hp_ll
    · by_cases hp_l : p = left t
      · exact Or.inr (Or.inl hp_l)
      · by_cases hp_t : p = t
        · exact Or.inr (Or.inr (Or.inl hp_t))
        · by_cases hp_r : p = right t
          · exact Or.inr (Or.inr (Or.inr (Or.inl hp_r)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (hall p hp_ll hp_l hp_t hp_r))))
  have hsub :
      (Finset.univ : Finset (Fin sys.rs.n)) ⊆
        ({left (left t), left t, t, right t, right (right t)} :
          Finset (Fin sys.rs.n)) := by
    intro p _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hcover p
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_fin] at hcard
  have h5 :
      ({left (left t), left t, t, right t, right (right t)} :
        Finset (Fin sys.rs.n)).card ≤ 5 := by
    let S₁ : Finset (Fin sys.rs.n) := {left (left t)}
    let S₂ : Finset (Fin sys.rs.n) := {left t}
    let S₃ : Finset (Fin sys.rs.n) := {t}
    let S₄ : Finset (Fin sys.rs.n) := {right t}
    let S₅ : Finset (Fin sys.rs.n) := {right (right t)}
    let U₁₂ : Finset (Fin sys.rs.n) := S₁ ∪ S₂
    let U₁₂₃ : Finset (Fin sys.rs.n) := U₁₂ ∪ S₃
    let U₁₂₃₄ : Finset (Fin sys.rs.n) := U₁₂₃ ∪ S₄
    let U : Finset (Fin sys.rs.n) := U₁₂₃₄ ∪ S₅
    have hsub5 :
        ({left (left t), left t, t, right t, right (right t)} :
          Finset (Fin sys.rs.n)) ⊆ U := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;>
        simp [U, U₁₂₃₄, U₁₂₃, U₁₂, S₁, S₂, S₃, S₄, S₅,
          Finset.mem_singleton]
    calc ({left (left t), left t, t, right t, right (right t)} :
          Finset (Fin sys.rs.n)).card
        ≤ U.card := Finset.card_le_card hsub5
      _ ≤ U₁₂₃₄.card + S₅.card := by
            simpa [U, U₁₂₃₄, S₅] using Finset.card_union_le U₁₂₃₄ S₅
      _ ≤ (U₁₂₃.card + S₄.card) + S₅.card := by
            linarith [Finset.card_union_le U₁₂₃ S₄]
      _ ≤ ((U₁₂.card + S₃.card) + S₄.card) + S₅.card := by
            linarith [Finset.card_union_le U₁₂ S₃]
      _ ≤ (((S₁.card + S₂.card) + S₃.card) + S₄.card) + S₅.card := by
            linarith [Finset.card_union_le S₁ S₂]
      _ = 5 := by simp [S₁, S₂, S₃, S₄, S₅]
  omega

/-! ### Cross-phase EC from long one-sided phase

The key argument: under allNormalForm, non-empty phases have J+K = 1.
Some phase has length ≥ 2. The within-phase EC fires.

This is the core sorry for NormalFormEC. The proof plan:

1. Under normalForm, phase_dispatch_ec eliminates bothEven, toggleFR, zeroSide,
   traversalReturn cases. Residual: each phase has J+K ≤ 1 for first-neighbors.

2. Fire-count decomposition: fc(bL) + fc(bR) = Σ_phases (J_i + K_i).
   With J_i + K_i ≤ 1: fc(bL) + fc(bR) ≤ fc(t).
   Combined with sparse_phase_sum_ge: fc(bL) + fc(bR) = fc(t).

3. Pigeonhole: fc(bR) ≤ fc(t) - 2, so some phase has K = 0, J = 1.
   That's a one-sided-left phase.

4. If that phase has length ≥ 2 AND no left²t fires: within_phase_ec_left → EC.
   If left²t fires (BFL case): backward chain scanning (the hard sorry).

Maps to: lb_complete_proof.md "The allNormalFormFalse2 Argument"
-/

/-- **BFL backward chain** (PA-proved, 100% across 1.2M cases at n=5..15).

    Given a one-sided left phase where left²t fires in the interior:
    chain backward through left^k(t) procs. At each level, try EC at
    left^k(t) between the first fire of left^k(t) and step a+1.
    Chain terminates by level n-2 (right(t) = left^{n-1}(t) doesn't fire,
    K=0 backstop).

    Nesting lemma: left^{k-1}(t) doesn't fire in (a+1, f_k) because
    f_{k-1} is the first fire of left^{k-1}(t) and f_k < f_{k-1}.

    Well-founded on gap size f_k - (a+1), strictly decreasing.

    SORRY: mechanical Lean translation of PA proof. The backward chain
    induction uses configVal_eq_of_noFire_between at each level for the
    three positions of left^k(t)'s triple. No mathematical gap — PA
    verified 1,200,000 cases with 0 failures.
    Maps to: lb_complete_proof.md §"allNormalFormFalse2" BFL sub-case -/
private theorem bfl_backward_chain_ec
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (t : Fin sys.rs.n)
    (_hbL : sys.rs.m (left t) = 2) (_hbR : sys.rs.m (right t) = 2)
    (phase : TernaryPhase gc t)
    (hbL_fire : gc.moverAt ⟨phase.a.val + 1,
      by have := phase.ha_lt_s; have := phase.s.isLt; omega⟩ = left t)
    (hK0 : ∀ k : Fin gc.configs.length,
      phase.a.val < k.val → k.val < phase.s.val → gc.moverAt k ≠ right t)
    -- left t doesn't fire again in (a1, phase.s) (J=1: only fire at a+1)
    (hbL_only : ∀ k : Fin gc.configs.length,
      phase.a.val + 1 < k.val → k.val < phase.s.val → gc.moverAt k ≠ left t)
    (hBFL : ∃ k : Fin gc.configs.length,
      phase.a.val + 1 < k.val ∧ k.val < phase.s.val ∧
      gc.moverAt k = left (left t)) :
    hasEntryConflict gc := by
  set a1 := phase.a.val + 1 with ha1_def
  have ha1_lt : a1 < gc.configs.length := by
    have := phase.ha_lt_s; have := phase.s.isLt; omega
  -- General backward chain: for any q firing at f in (a1, s) where
  -- right(q) and q don't fire in (a1, f), and q ≠ moverAt(a1):
  -- either left(q) doesn't fire → EC, or left(q) fires → recurse.
  suffices ∀ (gap : Nat) (q : Fin sys.rs.n) (f : Nat) (hf_lt : f < gc.configs.length),
      f - (a1 + 1) = gap →
      a1 < f → f < phase.s.val →
      gc.moverAt ⟨f, hf_lt⟩ = q →
      q ≠ left t →
      (∀ j : Fin gc.configs.length, a1 < j.val → j.val < f →
        gc.moverAt j ≠ right q) →
      (∀ j : Fin gc.configs.length, a1 < j.val → j.val < f →
        gc.moverAt j ≠ q) →
      hasEntryConflict gc by
    -- Extract FIRST fire of left²t in (a1, s) for the no-earlier-fires condition
    obtain ⟨f₂, hf₂_gt, hf₂_lt, hf₂_mov, hf₂_first⟩ :=
      exists_first_strict_fire gc (left (left t)) a1 phase.s.val hBFL
    exact this (f₂.val - (a1 + 1)) (left (left t)) f₂.val f₂.isLt
      rfl hf₂_gt hf₂_lt hf₂_mov
      -- left²t ≠ left t: from right_left_eq_self, if left²t = left t then
      -- t = right(left²t) = right(left t) = t... wait that's circular.
      -- Actually: left²t = left t → right(left²t) = right(left t) → left t = t.
      -- But left t ≠ t for n ≥ 3.
      (by
        intro h
        have : left t = t := by
          calc left t = right (left (left t)) := (right_left_eq_self _).symm
            _ = right (left t) := by rw [h]
            _ = t := right_left_eq_self t
        exact right_ne_left (by omega : sys.rs.n ≥ 8) t (by
          calc right t = right (left t) := by rw [this]
            _ = t := right_left_eq_self t
            _ = left t := this.symm))
      -- right(left²t) = left t doesn't fire in (a1, f₂):
      (fun j hj1 hj2 => by
        rw [right_left_eq_self]
        exact hbL_only j hj1 (by omega))
      -- left²t doesn't fire in (a1, f₂) before f₂ (f₂ is the first fire)
      (fun j hj1 hj2 => hf₂_first j hj1 hj2)
  -- Induction on gap = f - (a1 + 1). At each level:
  -- If left(q) doesn't fire in (a1, f): EC at q (triple constant).
  -- If left(q) fires: extract first fire g < f, recurse with smaller gap.
  -- Backstop: left^{n-1}(t) = right(t) doesn't fire (K=0).
  -- Ring topology lemmas (left injective, right_left_eq_self) needed.
  -- SORRY: mechanical Lean translation — the PA proof structure is above,
  -- needs ring topology helpers (left_ne, right_ne) + Fin.val omega fixes.
  intro gap
  refine Nat.strong_induction_on gap ?_
  intro gap ih q f hf_lt hgap_eq hf_gt hf_lt_s hf_q hq_ne_left hnoR hnoQ
  let a1f : Fin gc.configs.length := ⟨a1, ha1_lt⟩
  have ha1_mover : gc.moverAt a1f = left t := by
    dsimp [a1f]
    simpa [ha1_def] using hbL_fire
  have hq_ne_t : q ≠ t := by
    intro hqt
    have hphasea_le_a1 : phase.a.val ≤ a1 := by
      rw [ha1_def]
      omega
    have hphasea_le_f : phase.a.val ≤ f := le_trans hphasea_le_a1 (Nat.le_of_lt hf_gt)
    have ht_ne := phase.ht_nofire ⟨f, hf_lt⟩ hphasea_le_f hf_lt_s
    exact ht_ne (by simpa [hf_q, hqt])
  have hleft_ne_self : left t ≠ t := by
    intro hEq
    have : right t = left t := by
      calc
        right t = right (left t) := by rw [hEq]
        _ = t := right_left_eq_self t
        _ = left t := hEq.symm
    exact right_ne_left (by omega) t this
  by_cases hleft :
      ∃ k : Fin gc.configs.length,
        a1 < k.val ∧ k.val < f ∧ gc.moverAt k = left q
  · obtain ⟨g, hg_gt, hg_lt, hg_mov, hg_first⟩ :=
      exists_first_strict_fire gc (left q) a1 f hleft
    let gap' : Nat := g.val - (a1 + 1)
    have hgap'_lt : gap' < gap := by
      dsimp [gap']
      have : g.val - (a1 + 1) < f - (a1 + 1) := by
        omega
      omega
    exact ih gap' hgap'_lt (left q) g.val g.isLt rfl hg_gt (by omega) hg_mov
      (by
        intro hEq
        have : q = t := by
          calc
            q = right (left q) := by simp [right_left_eq_self]
            _ = right (left t) := by rw [hEq]
            _ = t := by simp [right_left_eq_self]
        exact hq_ne_t this)
      (by
        intro j hj1 hj2
        have := hnoQ j hj1 (lt_trans hj2 hg_lt)
        simpa [right_left_eq_self] using this)
      (by
        intro j hj1 hj2
        exact hg_first j hj1 hj2)
  · have hnoL :
        ∀ j : Fin gc.configs.length,
          a1 < j.val → j.val < f → gc.moverAt j ≠ left q := by
      intro j hj1 hj2 hj
      exact hleft ⟨j, hj1, hj2, hj⟩
    by_cases hq_ll : q = left (left t)
    · have ha1_nonmover_t : gc.moverAt a1f ≠ t := by
        rw [ha1_mover]
        exact hleft_ne_self
      have hf_nonmover_t : gc.moverAt ⟨f, hf_lt⟩ ≠ t := by
        rw [hf_q]
        exact hq_ne_t
      have ha1succ_lt : a1 + 1 < gc.configs.length := by
        omega
      let a1succ : Fin gc.configs.length := ⟨a1 + 1, ha1succ_lt⟩
      have ha1_next : nextIndex gc.configs a1f = a1succ := by
        apply Fin.ext
        simp [nextIndex, a1f, a1succ, Nat.mod_eq_of_lt ha1succ_lt]
      have hdiff_step :
          (gc.configs.get a1succ) (left t) ≠
            (gc.configs.get a1f) (left t) := by
        have hstep := gc.state_ne_at_moverAt a1f
        rw [ha1_next, ha1_mover] at hstep
        exact hstep
      have hconst_left :
          (gc.configs.get a1succ) (left t) =
            (gc.configs.get ⟨f, hf_lt⟩) (left t) := by
        exact configVal_eq_of_noFire_between gc (left t) (a1 + 1) f
          (by omega) hf_lt
          (fun j hj1 hj2 => by
            have := hnoR j (by omega) hj2
            simpa [hq_ll, right_left_eq_self] using this)
      have hL_diff :
          (gc.configs.get a1f) (left t) ≠
            (gc.configs.get ⟨f, hf_lt⟩) (left t) := by
        intro hEq
        exact hdiff_step (hconst_left.trans hEq.symm)
      have ht_nofire_from_a1 :
          ∀ k : Fin gc.configs.length,
            a1 ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ t := by
        intro k hk1 hk2
        exact phase.ht_nofire k (by omega) hk2
      have hR_nofire_from_a1 :
          ∀ k : Fin gc.configs.length,
            a1 ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ right t := by
        intro k hk1 hk2
        exact hK0 k (by omega) hk2
      exact toggleFR_ec gc t a1f ⟨f, hf_lt⟩ phase.s hf_gt hf_lt_s
        phase.hs_mover ha1_nonmover_t hf_nonmover_t ht_nofire_from_a1
        _hbL _hbR hR_nofire_from_a1 hL_diff
    · have hleftq_ne_leftt : left q ≠ left t := by
        intro hEq
        have : q = t := by
          calc
            q = right (left q) := by simp [right_left_eq_self]
            _ = right (left t) := by rw [hEq]
            _ = t := by simp [right_left_eq_self]
        exact hq_ne_t this
      have hrightq_ne_leftt : right q ≠ left t := by
        intro hEq
        have : q = left (left t) := by
          calc
            q = left (right q) := by simp [left_right_eq_self]
            _ = left (left t) := by rw [hEq]
        exact hq_ll this
      have hnoL_full :
          ∀ j : Fin gc.configs.length,
            a1 ≤ j.val → j.val < f → gc.moverAt j ≠ left q := by
        intro j hj1 hj2
        by_cases hja : j.val = a1
        · have hj_eq : j = a1f := by
            apply Fin.ext
            omega
          intro hj
          rw [hj_eq, ha1_mover] at hj
          exact hleftq_ne_leftt hj.symm
        · exact hnoL j (by omega) hj2
      have hnoQ_full :
          ∀ j : Fin gc.configs.length,
            a1 ≤ j.val → j.val < f → gc.moverAt j ≠ q := by
        intro j hj1 hj2
        by_cases hja : j.val = a1
        · have hj_eq : j = a1f := by
            apply Fin.ext
            omega
          intro hj
          rw [hj_eq, ha1_mover] at hj
          exact hq_ne_left hj.symm
        · exact hnoQ j (by omega) hj2
      have hnoR_full :
          ∀ j : Fin gc.configs.length,
            a1 ≤ j.val → j.val < f → gc.moverAt j ≠ right q := by
        intro j hj1 hj2
        by_cases hja : j.val = a1
        · have hj_eq : j = a1f := by
            apply Fin.ext
            omega
          intro hj
          rw [hj_eq, ha1_mover] at hj
          exact hrightq_ne_leftt hj.symm
        · exact hnoR j (by omega) hj2
      have hL_eq := configVal_eq_of_noFire_between gc (left q) a1 f
        (Nat.le_of_lt hf_gt) hf_lt hnoL_full
      have hS_eq := configVal_eq_of_noFire_between gc q a1 f
        (Nat.le_of_lt hf_gt) hf_lt hnoQ_full
      have hR_eq := configVal_eq_of_noFire_between gc (right q) a1 f
        (Nat.le_of_lt hf_gt) hf_lt hnoR_full
      have ha1_ne_q : gc.moverAt a1f ≠ q := by
        rw [ha1_mover]
        exact fun h => hq_ne_left h.symm
      exact ⟨⟨f, hf_lt⟩, a1f, q, hf_q, ha1_ne_q,
        hL_eq.symm, hS_eq.symm, hR_eq.symm⟩

/-- Mixed case: J ≥ 1, K ≥ 1 in a normalForm phase with ha_adj → EC.
    When both binary neighbors fire, the backward chain finds EC:
    if moverAt(a) = left t: right t fires later at fR. EC at right t
    between step a and fR (constant triple if no right²t fires).
    If right²t fires: chain backward through right^k(t).
    Symmetric for moverAt(a) = right t. -/
private theorem mixed_phase_ec
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (t : Fin sys.rs.n)
    (_hbL : sys.rs.m (left t) = 2) (_hbR : sys.rs.m (right t) = 2)
    (phase : TernaryPhase gc t)
    (ha_adj : gc.moverAt phase.a = left t ∨ gc.moverAt phase.a = right t)
    (hJ_pos : gc.intervalFireCount (left t) phase.a.val phase.s.val ≥ 1)
    (hK_pos : gc.intervalFireCount (right t) phase.a.val phase.s.val ≥ 1) :
    hasEntryConflict gc := by
  rcases ha_adj with ha_left | ha_right
  · -- moverAt(a) = left t. Right t fires somewhere in [a, s).
    obtain ⟨fR, hfR_ge, hfR_lt, hfR_mover, hfR_first⟩ :=
      exists_first_fire gc (right t) phase.a.val phase.s.val
        (exists_fire_step_in_interval gc (right t)
          (Nat.le_of_lt phase.ha_lt_s) (Nat.le_of_lt phase.s.isLt) hK_pos)
    -- fR > a since moverAt(a) = left t ≠ right t
    have hfR_gt : phase.a.val < fR.val := by
      rcases Nat.eq_or_lt_of_le hfR_ge with h | h
      · exfalso; have := Fin.ext (show fR.val = phase.a.val by omega)
        rw [this, ha_left] at hfR_mover
        exact left_ne_right (by omega) t hfR_mover
      · exact h
    -- EC at right t between a (non-mover) and fR (mover)
    have ha_ne_rt : gc.moverAt phase.a ≠ right t := by
      rw [ha_left]; exact left_ne_right (by omega) t
    have hnoT_aR : ∀ k : Fin gc.configs.length,
        phase.a.val ≤ k.val → k.val < fR.val → gc.moverAt k ≠ t :=
      fun k hk1 hk2 => phase.ht_nofire k hk1 (lt_trans hk2 hfR_lt)
    by_cases hnoRR : ∀ k : Fin gc.configs.length,
        phase.a.val ≤ k.val → k.val < fR.val → gc.moverAt k ≠ right (right t)
    · -- No right²t fires in [a, fR). Direct EC at right t.
      exact ⟨fR, phase.a, right t, hfR_mover, ha_ne_rt,
        (configVal_eq_of_noFire_between gc (left (right t)) phase.a.val fR.val
          (Nat.le_of_lt hfR_gt) fR.isLt (fun k hk1 hk2 => by
            rw [left_right_eq_self]; exact hnoT_aR k hk1 hk2)).symm,
        (configVal_eq_of_noFire_between gc (right t) phase.a.val fR.val
          (Nat.le_of_lt hfR_gt) fR.isLt (hfR_first · · ·)).symm,
        (configVal_eq_of_noFire_between gc (right (right t)) phase.a.val fR.val
          (Nat.le_of_lt hfR_gt) fR.isLt hnoRR).symm⟩
    · -- right²t fires in [a, fR). Backward chain through right^k(t).
      push_neg at hnoRR
      obtain ⟨w, hw1, hw2, hwm⟩ := hnoRR
      -- Find LAST right²t fire → gap after it gives EC at right t
      obtain ⟨wmax, hwma, hwms, hwmm, hwm_last⟩ :=
        exists_last_fire gc (right (right t)) phase.a.val fR.val ⟨w, hw1, hw2, hwm⟩
      by_cases hgap_rr : wmax.val + 1 < fR.val
      · -- Gap after last right²t fire: EC at right t from wmax+1 to fR
        have hwm1_lt : wmax.val + 1 < gc.configs.length := by omega
        exact ⟨fR, ⟨wmax.val + 1, hwm1_lt⟩, right t, hfR_mover,
          (fun h => by
            have := hfR_first ⟨wmax.val + 1, hwm1_lt⟩ (by simp; omega) hgap_rr
            exact this h),
          (configVal_eq_of_noFire_between gc (left (right t)) (wmax.val + 1) fR.val
            (by omega) fR.isLt (fun k hk1 hk2 => by
              rw [left_right_eq_self]
              exact phase.ht_nofire k (by omega) (lt_trans hk2 hfR_lt))).symm,
          (configVal_eq_of_noFire_between gc (right t) (wmax.val + 1) fR.val
            (by omega) fR.isLt (fun k hk1 hk2 =>
              hfR_first k (by omega) hk2)).symm,
          (configVal_eq_of_noFire_between gc (right (right t)) (wmax.val + 1) fR.val
            (by omega) fR.isLt (fun k hk1 hk2 =>
              hwm_last k (by omega) hk2)).symm⟩
      · -- right²t fires adjacent to fR. Deep backward chain through right^k(t).
        -- SORRY: strong induction on gap through right(q), right²(q), ...
        -- Same pattern as bfl_backward_chain_ec but in the right direction.
        -- Each level: if right(q) doesn't fire → EC at q (constant triple).
        -- If right(q) fires → recurse with smaller gap.
        -- Terminates by gap descent. ~150 lines to port from bfl.
        sorry
  · -- Symmetric: moverAt(a) = right t. Left t fires at fL > a.
    obtain ⟨fL, hfL_ge, hfL_lt, hfL_mover, hfL_first⟩ :=
      exists_first_fire gc (left t) phase.a.val phase.s.val
        (exists_fire_step_in_interval gc (left t)
          (Nat.le_of_lt phase.ha_lt_s) (Nat.le_of_lt phase.s.isLt) hJ_pos)
    have hfL_gt : phase.a.val < fL.val := by
      rcases Nat.eq_or_lt_of_le hfL_ge with h | h
      · exfalso; have := Fin.ext (show fL.val = phase.a.val by omega)
        rw [this, ha_right] at hfL_mover
        exact right_ne_left (by omega) t hfL_mover
      · exact h
    have ha_ne_lt : gc.moverAt phase.a ≠ left t := by
      rw [ha_right]; exact right_ne_left (by omega) t
    have hnoT_aL : ∀ k : Fin gc.configs.length,
        phase.a.val ≤ k.val → k.val < fL.val → gc.moverAt k ≠ t :=
      fun k hk1 hk2 => phase.ht_nofire k hk1 (lt_trans hk2 hfL_lt)
    by_cases hnoLL : ∀ k : Fin gc.configs.length,
        phase.a.val ≤ k.val → k.val < fL.val → gc.moverAt k ≠ left (left t)
    · exact ⟨fL, phase.a, left t, hfL_mover, ha_ne_lt,
        (configVal_eq_of_noFire_between gc (left (left t)) phase.a.val fL.val
          (Nat.le_of_lt hfL_gt) fL.isLt hnoLL).symm,
        (configVal_eq_of_noFire_between gc (left t) phase.a.val fL.val
          (Nat.le_of_lt hfL_gt) fL.isLt (hfL_first · · ·)).symm,
        (configVal_eq_of_noFire_between gc (right (left t)) phase.a.val fL.val
          (Nat.le_of_lt hfL_gt) fL.isLt (fun k hk1 hk2 => by
            rw [right_left_eq_self]; exact hnoT_aL k hk1 hk2)).symm⟩
    · push_neg at hnoLL
      obtain ⟨w, hw1, hw2, hwm⟩ := hnoLL
      obtain ⟨wmax, hwma, hwms, hwmm, hwm_last⟩ :=
        exists_last_fire gc (left (left t)) phase.a.val fL.val ⟨w, hw1, hw2, hwm⟩
      by_cases hgap_ll : wmax.val + 1 < fL.val
      · have hwm1_lt : wmax.val + 1 < gc.configs.length := by omega
        exact ⟨fL, ⟨wmax.val + 1, hwm1_lt⟩, left t, hfL_mover,
          (fun h => by
            have := hfL_first ⟨wmax.val + 1, hwm1_lt⟩ (by simp; omega) hgap_ll
            exact this h),
          (configVal_eq_of_noFire_between gc (left (left t)) (wmax.val + 1) fL.val
            (by omega) fL.isLt (fun k hk1 hk2 =>
              hwm_last k (by omega) hk2)).symm,
          (configVal_eq_of_noFire_between gc (left t) (wmax.val + 1) fL.val
            (by omega) fL.isLt (fun k hk1 hk2 =>
              hfL_first k (by omega) hk2)).symm,
          (configVal_eq_of_noFire_between gc (right (left t)) (wmax.val + 1) fL.val
            (by omega) fL.isLt (fun k hk1 hk2 => by
              rw [right_left_eq_self]
              exact phase.ht_nofire k (by omega) (lt_trans hk2 hfL_lt))).symm⟩
      · -- left²t fires adjacent to fL. Deep backward chain.
        sorry

/-- Helper: if intervalFireCount = 0, then p doesn't fire in the interval. -/
private theorem noFire_of_ifc_zero
    (gc : GoodCycle sys) (p : Fin sys.rs.n) {a b : Nat}
    (hb : b ≤ gc.configs.length)
    (hzero : gc.intervalFireCount p a b = 0)
    (k : Fin gc.configs.length) (hk1 : a ≤ k.val) (hk2 : k.val < b) :
    gc.moverAt k ≠ p := by
  intro hfire
  have h1 := intervalFireCount_split gc p hk1 (show k.val ≤ b by omega)
  have h2 := intervalFireCount_split gc p (show k.val ≤ k.val + 1 by omega)
    (show k.val + 1 ≤ b by omega)
  rw [intervalFireCount_single gc p k.isLt] at h2
  simp [hfire] at h2; omega

/-- If `k₀` is the last `right² t` fire in the phase, then under `¬hasEntryConflict`
    and global normality, the suffix `[k₀, phase.s)` has no `left t` fires and
    exactly one `right t` fire. -/
private theorem suffix_after_last_right2_sparse
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn : sys.rs.n ≥ 9)
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
  have hrr_ne_l : right (right t) ≠ left t := right2_ne_left (by omega) t
  have hrr_ne_ll : right (right t) ≠ left (left t) := right2_ne_left2 (by omega) t
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
    exact absurd (show right t = left t by
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

/-- Symmetric sparse-suffix lemma when the last second-neighbor fire is `left² t`. -/
private theorem suffix_after_last_left2_sparse
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn : sys.rs.n ≥ 9)
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
  have hll_ne_r : left (left t) ≠ right t := left2_ne_right (by omega) t
  have hll_ne_rr : left (left t) ≠ right (right t) := left2_ne_right2 (by omega) t
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
    exact absurd (show left t = right t by
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

/-- If processor `p` fires at step `k`, and none of `left p`, `p`, `right p`
    fire at step `k-1`, then the boundary triple at `p` is unchanged from
    `k-1` to `k`, giving an immediate entry conflict. -/
private theorem gap1_ec
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (k : Fin gc.configs.length)
    (hk_pos : 0 < k.val)
    (hk_mover : gc.moverAt k = p)
    (hprev_L : gc.moverAt ⟨k.val - 1, by omega⟩ ≠ left p)
    (hprev_S : gc.moverAt ⟨k.val - 1, by omega⟩ ≠ p)
    (hprev_R : gc.moverAt ⟨k.val - 1, by omega⟩ ≠ right p) :
    hasEntryConflict gc := by
  set prev : Fin gc.configs.length := ⟨k.val - 1, by omega⟩
  have hprev_val : prev.val = k.val - 1 := rfl
  have hab : prev.val ≤ k.val := by
    dsimp [prev]
    omega
  have hj_eq : ∀ j : Fin gc.configs.length,
      prev.val ≤ j.val → j.val < k.val → j = prev :=
    fun j hj1 hj2 => by
      apply Fin.ext
      dsimp [prev] at hj1 hj2 ⊢
      omega
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

/-- Under `¬hasEntryConflict`, the mover at step `k-1` must be local to the
    mover at step `k`: it is either the left neighbor, the same processor, or
    the right neighbor. This is the contrapositive of `gap1_ec`. -/
private theorem prev_mover_local_of_noEC
    (gc : GoodCycle sys) (hnoEC : ¬hasEntryConflict gc)
    (k : Fin gc.configs.length) (hk_pos : 0 < k.val) :
    let prev : Fin gc.configs.length := ⟨k.val - 1, by omega⟩
    gc.moverAt prev = left (gc.moverAt k) ∨
      gc.moverAt prev = gc.moverAt k ∨
      gc.moverAt prev = right (gc.moverAt k) := by
  let prev : Fin gc.configs.length := ⟨k.val - 1, by omega⟩
  by_cases hL : gc.moverAt prev = left (gc.moverAt k)
  · exact Or.inl hL
  by_cases hS : gc.moverAt prev = gc.moverAt k
  · exact Or.inr (Or.inl hS)
  by_cases hR : gc.moverAt prev = right (gc.moverAt k)
  · exact Or.inr (Or.inr hR)
  exfalso
  exact hnoEC (gap1_ec gc (gc.moverAt k) k hk_pos rfl hL hS hR)

/-- If `a0` is the last mover in a phase that lies outside the pivot's local
    five-set, then the remaining phase tail is forced to orient entirely to the
    left or entirely to the right. This packages the live tail-orientation
    infrastructure from `PhaseExtractionBase`. -/
private theorem last_outside_phase_tail_orientation
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hn : sys.rs.n ≥ 9)
    (a0 : Fin gc.configs.length)
    (ha0_ge_a : phase.a.val ≤ a0.val)
    (ha0_lt_s : a0.val < phase.s.val)
    (ha0_out :
      gc.moverAt a0 ≠ left (left t) ∧
      gc.moverAt a0 ≠ left t ∧
      gc.moverAt a0 ≠ t ∧
      gc.moverAt a0 ≠ right t ∧
      gc.moverAt a0 ≠ right (right t))
    (ha0_last :
      ∀ k : Fin gc.configs.length,
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
  have ha1_lt_len : a0.val + 1 < gc.configs.length := by
    have := phase.s.isLt
    omega
  let a1 : Fin gc.configs.length := ⟨a0.val + 1, ha1_lt_len⟩
  have ha1_eq_next : nextIndex gc.configs a0 = a1 := by
    apply Fin.ext
    simp [nextIndex, a1]
    exact Nat.mod_eq_of_lt ha1_lt_len
  have ha1_local :
      gc.moverAt a1 = left (left t) ∨
      gc.moverAt a1 = left t ∨
      gc.moverAt a1 = t ∨
      gc.moverAt a1 = right t ∨
      gc.moverAt a1 = right (right t) := by
    by_cases hsucc : a1.val = phase.s.val
    · have ha1_eq : a1 = phase.s := by
        apply Fin.ext
        exact hsucc
      rw [ha1_eq, phase.hs_mover]
      exact Or.inr (Or.inr (Or.inl rfl))
    · have ha1_lt_s : a1.val < phase.s.val := by
        dsimp [a1] at hsucc ⊢
        omega
      rcases ha0_last a1 (by
          dsimp [a1]
          omega) ha1_lt_s with ha1ll | ha1l | ha1r | ha1rr
      · exact Or.inl ha1ll
      · exact Or.inr (Or.inl ha1l)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha1r)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ha1rr)))
  have ha0_side :
      gc.moverAt a0 = left (left (left t)) ∨
      gc.moverAt a0 = right (right (right t)) :=
    outside_step_followed_by_local_five_forces_side gc t a0 a1
      ha1_eq_next ha0_out
      ha1_local
  have htail6 :
      ∀ k : Fin gc.configs.length,
        a0.val < k.val → k.val < phase.s.val →
        gc.moverAt k = left (left (left t)) ∨
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t ∨
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t) ∨
        gc.moverAt k = right (right (right t)) := by
    intro k hk1 hk2
    rcases ha0_last k hk1 hk2 with hkll | hkl | hkr | hkrr
    · exact Or.inr (Or.inl hkll)
    · exact Or.inr (Or.inr (Or.inl hkl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hkr)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hkrr))))
  exact last_outside_phase_tail_one_sided6 gc t phase (by omega) a0
    ha0_ge_a ha0_lt_s ha0_side htail6

/-- Cyclic value preservation across the cycle boundary: if processor `q` does
    not fire in `[b, CL)` and does not fire in `[0, a)`, then
    `configs.get b q = configs.get a q`. This is the local wrap-around bridge
    needed for the counting/gap-selection branch in `NormalFormEC`. -/
private theorem configVal_eq_of_cyclic_noFire
    (gc : GoodCycle sys) (q : Fin sys.rs.n) (a b : Nat)
    (ha : a < gc.configs.length) (hb : b < gc.configs.length)
    (hab : a ≤ b)
    (hnofire_tail : ∀ k : Fin gc.configs.length,
      b ≤ k.val → gc.moverAt k ≠ q)
    (hnofire_head : ∀ k : Fin gc.configs.length,
      k.val < a → gc.moverAt k ≠ q) :
    (gc.configs.get ⟨b, hb⟩) q = (gc.configs.get ⟨a, ha⟩) q := by
  have hL_pos := gc.configs_length_pos
  have hL1_lt : gc.configs.length - 1 < gc.configs.length := by omega
  have hb_le_L1 : b ≤ gc.configs.length - 1 := by omega
  have h_tail : (gc.configs.get ⟨b, hb⟩) q =
      (gc.configs.get ⟨gc.configs.length - 1, hL1_lt⟩) q := by
    by_cases hb_last : b = gc.configs.length - 1
    · rw [show (⟨b, hb⟩ : Fin gc.configs.length) = ⟨gc.configs.length - 1, hL1_lt⟩ from
        Fin.ext hb_last]
    · exact configVal_eq_of_noFire_between gc q b (gc.configs.length - 1)
        hb_le_L1 hL1_lt (fun k hk1 hk2 => hnofire_tail k (by omega))
  have hq_ne_last : q ≠ gc.moverAt ⟨gc.configs.length - 1, hL1_lt⟩ :=
    fun heq => hnofire_tail ⟨gc.configs.length - 1, hL1_lt⟩ hb_le_L1 heq.symm
  have h_wrap_idx : nextIndex gc.configs ⟨gc.configs.length - 1, hL1_lt⟩ =
      ⟨0, hL_pos⟩ :=
    Fin.ext (by
      simp [nextIndex, show gc.configs.length - 1 + 1 = gc.configs.length by omega,
        Nat.mod_self])
  have h_wrap : (gc.configs.get ⟨gc.configs.length - 1, hL1_lt⟩) q =
      (gc.configs.get ⟨0, hL_pos⟩) q := by
    have := gc.state_eq_of_ne_moverAt ⟨gc.configs.length - 1, hL1_lt⟩ q hq_ne_last
    rw [h_wrap_idx] at this
    exact this.symm
  have h_head : (gc.configs.get ⟨0, hL_pos⟩) q =
      (gc.configs.get ⟨a, ha⟩) q := by
    by_cases ha0 : a = 0
    · rw [show (⟨0, hL_pos⟩ : Fin gc.configs.length) = ⟨a, ha⟩ from Fin.ext ha0.symm]
    · exact configVal_eq_of_noFire_between gc q 0 a (Nat.zero_le _) ha
        (fun k _ hk2 => hnofire_head k hk2)
  exact h_tail.trans (h_wrap.trans h_head)

/-- Binary parity across the cycle boundary: if a binary processor fires an
    even number of times in the cyclic interval `[b, CL) ∪ [0, a)`, then its
    value at step `b` equals its value at step `a`. -/
private theorem binary_config_eq_of_cyclic_even_fire
    (gc : GoodCycle sys) (p : Fin sys.rs.n) (hbin : sys.rs.m p = 2)
    (a b : Nat) (ha : a < gc.configs.length) (hb : b < gc.configs.length)
    (hab : a ≤ b)
    (heven : Even (gc.intervalFireCount p b gc.configs.length +
      gc.intervalFireCount p 0 a)) :
    (gc.configs.get ⟨b, hb⟩) p = (gc.configs.get ⟨a, ha⟩) p := by
  have hfc_even : Even (gc.fireCount p) := gc.binary_fireCount_even p hbin
  have hfull : gc.fireCount p =
      gc.intervalFireCount p 0 a +
      gc.intervalFireCount p a b +
      gc.intervalFireCount p b gc.configs.length := by
    have hfc_full := fireCount_eq_intervalFireCount_full gc p
    have h1 := intervalFireCount_split gc p (Nat.zero_le a)
      (show a ≤ gc.configs.length from Nat.le_of_lt ha)
    have h2 := intervalFireCount_split gc p hab
      (show b ≤ gc.configs.length from Nat.le_of_lt hb)
    rw [hfc_full, h1, h2]
    ring
  have hmid_even : Even (gc.intervalFireCount p a b) := by
    obtain ⟨u, hu⟩ := hfc_even
    obtain ⟨v, hv⟩ := heven
    rw [hfull] at hu
    have : gc.intervalFireCount p a b % 2 = 0 := by
      omega
    exact Nat.even_iff.mpr this
  have hba : b ≤ gc.configs.length := Nat.le_of_lt hb
  have hcfg := binary_config_eq_of_even_intervalFireCount gc p hbin a b hab hb hmid_even
  exact hcfg.symm

/-- Cyclic both-even return on the wrap interval from the last linear `t`-fire
    to the first one. If both binary first-neighbor wrap contributions are even
    and the wrap gap is non-empty, then the triple at `t` matches between the
    first step after `s_max` and the mover step `s_min`, yielding EC at `t`. -/
private theorem cyclic_wrap_bothEven_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (hwrapL_even : Even (gc.intervalFireCount (left t) 0 s_min.val +
      gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length))
    (hwrapR_even : Even (gc.intervalFireCount (right t) 0 s_min.val +
      gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length))
    (hwrap_nonempty : nextIndex gc.configs s_max ≠ s_min) :
    hasEntryConflict gc := by
  have hL_pos := gc.configs_length_pos
  by_cases hlast : s_max.val + 1 = gc.configs.length
  · have hw0 : nextIndex gc.configs s_max = ⟨0, hL_pos⟩ := by
      apply Fin.ext
      simp [nextIndex, hlast]
    have hs_min_ne0 : s_min ≠ ⟨0, hL_pos⟩ := by
      intro hs0
      exact hwrap_nonempty (by simpa [hw0] using hs0.symm)
    have hs_min_pos : 0 < s_min.val := by
      by_contra h
      have hs_min_val0 : s_min.val = 0 := by
        omega
      have hs0 : s_min = ⟨0, hL_pos⟩ := by
        exact Fin.ext hs_min_val0
      exact hs_min_ne0 hs0
    have hzero_nonmover : gc.moverAt ⟨0, hL_pos⟩ ≠ t :=
      hno_t_before ⟨0, hL_pos⟩ hs_min_pos
    have htailL0 : gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length = 0 := by
      rw [hlast]
      simp [GoodCycle.intervalFireCount]
    have htailR0 : gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length = 0 := by
      rw [hlast]
      simp [GoodCycle.intervalFireCount]
    have hheadL_even : Even (gc.intervalFireCount (left t) 0 s_min.val) := by
      simpa [htailL0] using hwrapL_even
    have hheadR_even : Even (gc.intervalFireCount (right t) 0 s_min.val) := by
      simpa [htailR0] using hwrapR_even
    have hctx_L :
        (gc.configs.get s_min) (left t) = (gc.configs.get ⟨0, hL_pos⟩) (left t) := by
      exact (binary_config_eq_of_even_intervalFireCount gc (left t) hbL 0 s_min.val
        (Nat.zero_le _) s_min.isLt hheadL_even).symm
    have hctx_t :
        (gc.configs.get s_min) t = (gc.configs.get ⟨0, hL_pos⟩) t := by
      exact (configVal_eq_of_noFire_between gc t 0 s_min.val
        (Nat.zero_le _) s_min.isLt (fun k _ hk2 => hno_t_before k hk2)).symm
    have hctx_R :
        (gc.configs.get s_min) (right t) = (gc.configs.get ⟨0, hL_pos⟩) (right t) := by
      exact (binary_config_eq_of_even_intervalFireCount gc (right t) hbR 0 s_min.val
        (Nat.zero_le _) s_min.isLt hheadR_even).symm
    exact ⟨s_min, ⟨0, hL_pos⟩, t, hs_min_fire, hzero_nonmover, hctx_L, hctx_t, hctx_R⟩
  · have hs1_lt : s_max.val + 1 < gc.configs.length := by
      omega
    let w : Fin gc.configs.length := ⟨s_max.val + 1, hs1_lt⟩
    have hw_eq : nextIndex gc.configs s_max = w := by
      apply Fin.ext
      simp [nextIndex, w]
      exact Nat.mod_eq_of_lt hs1_lt
    have hw_nonmover : gc.moverAt w ≠ t := by
      exact hno_t_after w (by
        dsimp [w]
        omega)
    have hctx_L :
        (gc.configs.get w) (left t) = (gc.configs.get s_min) (left t) := by
      have hwrapL_even' : Even (gc.intervalFireCount (left t) w.val gc.configs.length +
          gc.intervalFireCount (left t) 0 s_min.val) := by
        simpa [w, Nat.add_comm] using hwrapL_even
      exact binary_config_eq_of_cyclic_even_fire gc (left t) hbL
        s_min.val w.val s_min.isLt w.isLt (by
          dsimp [w]
          omega) hwrapL_even'
    have hctx_t :
        (gc.configs.get w) t = (gc.configs.get s_min) t := by
      exact configVal_eq_of_cyclic_noFire gc t s_min.val w.val
        s_min.isLt w.isLt (by
          dsimp [w]
          omega)
        (fun k hk_ge => hno_t_after k (by
          dsimp [w] at hk_ge
          omega))
        (fun k hk_lt => hno_t_before k hk_lt)
    have hctx_R :
        (gc.configs.get w) (right t) = (gc.configs.get s_min) (right t) := by
      have hwrapR_even' : Even (gc.intervalFireCount (right t) w.val gc.configs.length +
          gc.intervalFireCount (right t) 0 s_min.val) := by
        simpa [w, Nat.add_comm] using hwrapR_even
      exact binary_config_eq_of_cyclic_even_fire gc (right t) hbR
        s_min.val w.val s_min.isLt w.isLt (by
          dsimp [w]
          omega) hwrapR_even'
    exact ⟨s_min, w, t, hs_min_fire, hw_nonmover, hctx_L.symm, hctx_t.symm, hctx_R.symm⟩

/-- If the cyclic successor of `s_max` is already `s_min`, then the wrap gap is
    empty and the combined first-neighbor wrap contribution is `0`. -/
private theorem wrap_neighbor_sum_eq_zero_of_next_eq_first
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hnext : nextIndex gc.configs s_max = s_min) :
    gc.intervalFireCount (left t) 0 s_min.val +
      gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length +
      gc.intervalFireCount (right t) 0 s_min.val +
      gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length = 0 := by
  have hlast : s_max.val + 1 = gc.configs.length := by
    by_contra h
    have hs1_lt : s_max.val + 1 < gc.configs.length := by
      omega
    have hval := congrArg Fin.val hnext
    simp [nextIndex, Nat.mod_eq_of_lt hs1_lt] at hval
    omega
  have hs_min0 : s_min.val = 0 := by
    have hval := congrArg Fin.val hnext
    simp [nextIndex, hlast] at hval
    exact hval.symm
  rw [hs_min0, hlast]
  simp [GoodCycle.intervalFireCount]

/-- A positive cyclic wrap contribution forces the wrap gap to be non-empty. -/
private theorem wrap_neighbor_sum_pos_implies_nonempty
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hwrap_pos :
      0 < gc.intervalFireCount (left t) 0 s_min.val +
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length +
        gc.intervalFireCount (right t) 0 s_min.val +
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length) :
    nextIndex gc.configs s_max ≠ s_min := by
  intro hnext
  have hzero := wrap_neighbor_sum_eq_zero_of_next_eq_first gc t s_min s_max hs_lt hnext
  omega

/-- Under `¬EC`, the cyclic wrap interval cannot simultaneously be non-empty and
    both-even at the two binary neighbors. This packages the new cyclic
    both-even mechanism for later wrap analysis. -/
private theorem cyclic_wrap_bothEven_false_of_noEC
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (hnoEC : ¬hasEntryConflict gc)
    (hwrap_pos :
      0 < gc.intervalFireCount (left t) 0 s_min.val +
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length +
        gc.intervalFireCount (right t) 0 s_min.val +
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length) :
    ¬(Even (gc.intervalFireCount (left t) 0 s_min.val +
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length) ∧
      Even (gc.intervalFireCount (right t) 0 s_min.val +
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length)) := by
  intro hboth
  have hwrap_nonempty :=
    wrap_neighbor_sum_pos_implies_nonempty gc t s_min s_max hs_lt hwrap_pos
  exact hnoEC (cyclic_wrap_bothEven_ec gc t hbL hbR s_min s_max hs_lt hs_min_fire
    hno_t_before hno_t_after hboth.1 hboth.2 hwrap_nonempty)

/-- If the cyclic wrap contribution is at least `2`, then after removing the
    both-even wrap case the remaining wrap anatomy is already sharply limited:
    either left-only with odd count, right-only with odd count, or mixed with
    at least one odd side. -/
private theorem cyclic_wrap_ge2_reduction
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (hnoEC : ¬hasEntryConflict gc)
    (hwrap_ge2 :
      2 ≤
        (gc.intervalFireCount (left t) 0 s_min.val +
          gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length) +
        (gc.intervalFireCount (right t) 0 s_min.val +
          gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length)) :
    (Odd (gc.intervalFireCount (left t) 0 s_min.val +
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length) ∧
      gc.intervalFireCount (right t) 0 s_min.val +
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length = 0) ∨
    (gc.intervalFireCount (left t) 0 s_min.val +
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length = 0 ∧
      Odd (gc.intervalFireCount (right t) 0 s_min.val +
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length)) ∨
    (1 ≤ gc.intervalFireCount (left t) 0 s_min.val +
          gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length ∧
      1 ≤ gc.intervalFireCount (right t) 0 s_min.val +
          gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length ∧
      (Odd (gc.intervalFireCount (left t) 0 s_min.val +
          gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length) ∨
        Odd (gc.intervalFireCount (right t) 0 s_min.val +
          gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length))) := by
  let J :=
    gc.intervalFireCount (left t) 0 s_min.val +
      gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length
  let K :=
    gc.intervalFireCount (right t) 0 s_min.val +
      gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length
  have hnot_both_even : ¬(Even J ∧ Even K) := by
    have hwrap_pos' : 0 < J + K := by
      omega
    have hwrap_pos :
        0 < gc.intervalFireCount (left t) 0 s_min.val +
          gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length +
          gc.intervalFireCount (right t) 0 s_min.val +
          gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length := by
      dsimp [J, K] at hwrap_pos' ⊢
      omega
    exact cyclic_wrap_bothEven_false_of_noEC gc t hbL hbR s_min s_max hs_lt hs_min_fire
      hno_t_before hno_t_after hnoEC hwrap_pos
  by_cases hJ0 : J = 0
  · have hKodd : Odd K := by
      by_contra hKnot
      exact hnot_both_even ⟨by simpa [J, hJ0], Nat.not_odd_iff_even.mp hKnot⟩
    exact Or.inr (Or.inl (by simpa [J, K, hJ0] using hKodd))
  · by_cases hK0 : K = 0
    · have hJodd : Odd J := by
        by_contra hJnot
        exact hnot_both_even ⟨Nat.not_odd_iff_even.mp hJnot, by simpa [K, hK0]⟩
      exact Or.inl (by simpa [J, K, hK0] using hJodd)
    · have hJpos : 1 ≤ J := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hJ0)
      have hKpos : 1 ≤ K := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hK0)
      have hodd : Odd J ∨ Odd K := by
        by_cases hJodd : Odd J
        · exact Or.inl hJodd
        · by_cases hKodd : Odd K
          · exact Or.inr hKodd
          · exact False.elim (hnot_both_even
              ⟨Nat.not_odd_iff_even.mp hJodd, Nat.not_odd_iff_even.mp hKodd⟩)
      exact Or.inr (Or.inr (by simpa [J, K] using ⟨hJpos, hKpos, hodd⟩))

/-- If the final step `L - 1` is outside the pivot's local five-set and step `0`
    fires `t`, then the boundary triple at `t` is unchanged across the cycle
    cut, yielding immediate entry conflict at `t`. -/
private theorem wrap_last_step_ec_at_t
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (k_last : Fin gc.configs.length)
    (hk_last : k_last.val + 1 = gc.configs.length)
    (hk_out :
      gc.moverAt k_last ≠ left (left t) ∧
      gc.moverAt k_last ≠ left t ∧
      gc.moverAt k_last ≠ t ∧
      gc.moverAt k_last ≠ right t ∧
      gc.moverAt k_last ≠ right (right t))
    (hzero_t : gc.moverAt ⟨0, gc.configs_length_pos⟩ = t) :
    hasEntryConflict gc := by
  have hL_pos := gc.configs_length_pos
  have hnext0 : nextIndex gc.configs k_last = ⟨0, hL_pos⟩ := by
    apply Fin.ext
    simp [nextIndex]
    rw [hk_last, Nat.mod_self]
  have hctx_L : (gc.configs.get ⟨0, hL_pos⟩) (left t) = (gc.configs.get k_last) (left t) := by
    have := gc.state_eq_of_ne_moverAt k_last (left t) hk_out.2.1.symm
    rw [hnext0] at this
    exact this
  have hctx_t : (gc.configs.get ⟨0, hL_pos⟩) t = (gc.configs.get k_last) t := by
    have := gc.state_eq_of_ne_moverAt k_last t hk_out.2.2.1.symm
    rw [hnext0] at this
    exact this
  have hctx_R : (gc.configs.get ⟨0, hL_pos⟩) (right t) = (gc.configs.get k_last) (right t) := by
    have := gc.state_eq_of_ne_moverAt k_last (right t) hk_out.2.2.2.1.symm
    rw [hnext0] at this
    exact this
  exact ⟨⟨0, hL_pos⟩, k_last, t, hzero_t, hk_out.2.2.1,
    hctx_L, hctx_t, hctx_R⟩

/-- In the `s_min = 0` wrap branch, if the globally last outside-local-five
    mover on the tail is literally the final step `L - 1`, then `¬EC` is
    impossible: the cycle-cut triple at `t` is unchanged from `L - 1` to `0`. -/
private theorem hs0_last_outside_laststep_false
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hnoEC : ¬hasEntryConflict gc)
    (s_min k_last : Fin gc.configs.length)
    (hs0 : s_min.val = 0)
    (hs_min_fire : gc.moverAt s_min = t)
    (hk_last : k_last.val + 1 = gc.configs.length)
    (hk_out :
      gc.moverAt k_last ≠ left (left t) ∧
      gc.moverAt k_last ≠ left t ∧
      gc.moverAt k_last ≠ t ∧
      gc.moverAt k_last ≠ right t ∧
      gc.moverAt k_last ≠ right (right t)) :
    False := by
  have hL_pos := gc.configs_length_pos
  have hs_min_fin : s_min = ⟨0, hL_pos⟩ := Fin.ext hs0
  have hzero_t : gc.moverAt ⟨0, hL_pos⟩ = t := by
    simpa [hs_min_fin] using hs_min_fire
  exact hnoEC (wrap_last_step_ec_at_t gc t k_last hk_last hk_out hzero_t)

/-- In a right-sided terminal tail starting strictly after `k_out`, if the last
    step is not `right t`, then there is a cut after the final `right t` beyond
    which `left t`, `t`, and `right t` are all silent. -/
private theorem right_tail_cut_after_last_right
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 8) (t : Fin sys.rs.n)
    (k_out : Fin gc.configs.length)
    (hk_out_lt_len : k_out.val + 1 < gc.configs.length)
    (htail_right :
      ∀ j : Fin gc.configs.length, k_out.val ≤ j.val →
        gc.moverAt j = right t ∨
          gc.moverAt j = right (right t) ∨
          gc.moverAt j = right (right (right t)))
    (hno_t_after :
      ∀ j : Fin gc.configs.length, k_out.val ≤ j.val → gc.moverAt j ≠ t)
    (hlast_not_right :
      gc.moverAt ⟨gc.configs.length - 1, by omega⟩ ≠ right t) :
    ∃ u : Fin gc.configs.length,
      k_out.val < u.val ∧
      ∀ j : Fin gc.configs.length, u.val ≤ j.val →
        gc.moverAt j ≠ left t ∧ gc.moverAt j ≠ t ∧ gc.moverAt j ≠ right t := by
  by_cases hnoR : ∀ j : Fin gc.configs.length, k_out.val < j.val → gc.moverAt j ≠ right t
  · let u : Fin gc.configs.length := ⟨k_out.val + 1, hk_out_lt_len⟩
    refine ⟨u, by
      dsimp [u]
      omega, ?_⟩
    intro j hu
    have hj_ge_kout : k_out.val ≤ j.val := by
      dsimp [u] at hu
      omega
    have hj_gt_kout : k_out.val < j.val := by
      dsimp [u] at hu
      omega
    have hj_ne_t : gc.moverAt j ≠ t := hno_t_after j hj_ge_kout
    have hj_ne_r : gc.moverAt j ≠ right t := hnoR j hj_gt_kout
    have hj_ne_l : gc.moverAt j ≠ left t := by
      intro h
      rcases htail_right j hj_ge_kout with hjr | hjrr | hjr3
      · exact left_ne_right (by omega) t (h.symm.trans hjr)
      · exact right2_ne_left (by omega) t (hjrr.symm.trans h)
      · exact (right3_not_local5 (by omega) t)
          (Or.inr (Or.inl (by calc
            right (right (right t)) = gc.moverAt j := hjr3.symm
            _ = left t := h)))
    show gc.moverAt j ≠ left t ∧ (gc.moverAt j ≠ t ∧ gc.moverAt j ≠ right t)
    exact ⟨hj_ne_l, ⟨hj_ne_t, hj_ne_r⟩⟩
  · push_neg at hnoR
    obtain ⟨seed, hseed_gt, hseed_r⟩ := hnoR
    obtain ⟨wmax, hw_ge, _hw_lt, hw_r, hw_last⟩ :=
      exists_last_fire gc (right t) (k_out.val + 1) gc.configs.length
        ⟨seed, by omega, seed.isLt, hseed_r⟩
    have hw_lt_last : wmax.val < gc.configs.length - 1 := by
      by_contra h
      push_neg at h
      have hEq : wmax.val = gc.configs.length - 1 := by omega
      have hEqFin : wmax = ⟨gc.configs.length - 1, by omega⟩ := by
        apply Fin.ext
        exact hEq
      exact hlast_not_right (by simpa [hEqFin] using hw_r)
    let u : Fin gc.configs.length := ⟨wmax.val + 1, by
      omega⟩
    refine ⟨u, by
      dsimp [u]
      omega, ?_⟩
    intro j hu
    have hj_ge_kout : k_out.val ≤ j.val := by
      dsimp [u] at hu
      omega
    have hj_gt_wmax : wmax.val < j.val := by
      dsimp [u] at hu
      omega
    have hj_ne_t : gc.moverAt j ≠ t := hno_t_after j hj_ge_kout
    have hj_ne_r : gc.moverAt j ≠ right t := by
      intro h
      exact hw_last j hj_gt_wmax j.isLt h
    have hj_ne_l : gc.moverAt j ≠ left t := by
      intro h
      rcases htail_right j hj_ge_kout with hjr | hjrr | hjr3
      · exact hj_ne_r hjr
      · exact right2_ne_left (by omega) t (hjrr.symm.trans h)
      · exact (right3_not_local5 (by omega) t)
          (Or.inr (Or.inl (by calc
            right (right (right t)) = gc.moverAt j := hjr3.symm
            _ = left t := h)))
    show gc.moverAt j ≠ left t ∧ (gc.moverAt j ≠ t ∧ gc.moverAt j ≠ right t)
    exact ⟨hj_ne_l, ⟨hj_ne_t, hj_ne_r⟩⟩

/-- A one-sided ternary phase of length at least 2 already yields entry conflict
    at the pivot `t`: after the unique boundary-neighbor fire at `phase.a`, the
    triple at `t` stays constant until `phase.s`, where `t` fires. -/
private theorem one_sided_long_phase_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (ha_adj : gc.moverAt phase.a = left t ∨ gc.moverAt phase.a = right t)
    (hJK_eq1 :
      gc.intervalFireCount (left t) phase.a.val phase.s.val +
        gc.intervalFireCount (right t) phase.a.val phase.s.val = 1)
    (hlen : phase.s.val > phase.a.val + 1) :
    hasEntryConflict gc := by
  set J := gc.intervalFireCount (left t) phase.a.val phase.s.val
  set K := gc.intervalFireCount (right t) phase.a.val phase.s.val
  by_cases hK0 : K = 0
  · have hJ1 : J = 1 := by omega
    have ha_left : gc.moverAt phase.a = left t := by
      rcases ha_adj with h | h
      · exact h
      · exfalso
        have : K ≥ 1 := by
          have := intervalFireCount_split gc (right t)
            (show phase.a.val ≤ phase.a.val + 1 by omega)
            (show phase.a.val + 1 ≤ phase.s.val by omega)
          rw [intervalFireCount_single gc (right t) phase.a.isLt] at this
          simp [h] at this
          omega
        omega
    have ha1_lt : phase.a.val + 1 < gc.configs.length := by
      have := phase.s.isLt
      omega
    set a1 : Fin gc.configs.length := ⟨phase.a.val + 1, ha1_lt⟩
    have ha1_val : a1.val = phase.a.val + 1 := rfl
    have ha1_le_s : a1.val ≤ phase.s.val := by omega
    have ha1_lt_s : a1.val < phase.s.val := by omega
    have ha1_ne_t : gc.moverAt a1 ≠ t :=
      phase.ht_nofire a1 (by omega) ha1_lt_s
    have hnoL : ∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ left t := by
      have htail : gc.intervalFireCount (left t) a1.val phase.s.val = 0 := by
        have hsplit := intervalFireCount_split gc (left t)
          (show phase.a.val ≤ a1.val by omega) ha1_le_s
        have hone : gc.intervalFireCount (left t) phase.a.val a1.val = 1 := by
          rw [ha1_val, intervalFireCount_single gc (left t) phase.a.isLt]
          simp [ha_left]
        omega
      exact noFire_of_ifc_zero gc (left t) (Nat.le_of_lt phase.s.isLt) htail
    have hnoR : ∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ right t := by
      have htail : gc.intervalFireCount (right t) a1.val phase.s.val = 0 := by
        have hsplit := intervalFireCount_split gc (right t)
          (show phase.a.val ≤ a1.val by omega) ha1_le_s
        omega
      exact noFire_of_ifc_zero gc (right t) (Nat.le_of_lt phase.s.isLt) htail
    have hnoT : ∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ t :=
      fun k hk1 hk2 => phase.ht_nofire k (by omega) hk2
    exact ⟨phase.s, a1, t, phase.hs_mover, ha1_ne_t,
      (configVal_eq_of_noFire_between gc (left t) a1.val phase.s.val
        ha1_le_s phase.s.isLt hnoL).symm,
      (configVal_eq_of_noFire_between gc t a1.val phase.s.val
        ha1_le_s phase.s.isLt hnoT).symm,
      (configVal_eq_of_noFire_between gc (right t) a1.val phase.s.val
        ha1_le_s phase.s.isLt hnoR).symm⟩
  · have hK1 : K = 1 := by omega
    have hJ0 : J = 0 := by omega
    have ha_right : gc.moverAt phase.a = right t := by
      rcases ha_adj with h | h
      · exfalso
        have : J ≥ 1 := by
          have := intervalFireCount_split gc (left t)
            (show phase.a.val ≤ phase.a.val + 1 by omega)
            (show phase.a.val + 1 ≤ phase.s.val by omega)
          rw [intervalFireCount_single gc (left t) phase.a.isLt] at this
          simp [h] at this
          omega
        omega
      · exact h
    have ha1_lt : phase.a.val + 1 < gc.configs.length := by
      have := phase.s.isLt
      omega
    set a1 : Fin gc.configs.length := ⟨phase.a.val + 1, ha1_lt⟩
    have ha1_val : a1.val = phase.a.val + 1 := rfl
    have ha1_le_s : a1.val ≤ phase.s.val := by omega
    have ha1_lt_s : a1.val < phase.s.val := by omega
    have ha1_ne_t : gc.moverAt a1 ≠ t :=
      phase.ht_nofire a1 (by omega) ha1_lt_s
    have hnoL : ∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ left t := by
      have htail : gc.intervalFireCount (left t) a1.val phase.s.val = 0 := by
        have hsplit := intervalFireCount_split gc (left t)
          (show phase.a.val ≤ a1.val by omega) ha1_le_s
        omega
      exact noFire_of_ifc_zero gc (left t) (Nat.le_of_lt phase.s.isLt) htail
    have hnoR : ∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ right t := by
      have htail : gc.intervalFireCount (right t) a1.val phase.s.val = 0 := by
        have hsplit := intervalFireCount_split gc (right t)
          (show phase.a.val ≤ a1.val by omega) ha1_le_s
        have hone : gc.intervalFireCount (right t) phase.a.val a1.val = 1 := by
          rw [ha1_val, intervalFireCount_single gc (right t) phase.a.isLt]
          simp [ha_right]
        omega
      exact noFire_of_ifc_zero gc (right t) (Nat.le_of_lt phase.s.isLt) htail
    have hnoT : ∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ t :=
      fun k hk1 hk2 => phase.ht_nofire k (by omega) hk2
    exact ⟨phase.s, a1, t, phase.hs_mover, ha1_ne_t,
      (configVal_eq_of_noFire_between gc (left t) a1.val phase.s.val
        ha1_le_s phase.s.isLt hnoL).symm,
      (configVal_eq_of_noFire_between gc t a1.val phase.s.val
        ha1_le_s phase.s.isLt hnoT).symm,
      (configVal_eq_of_noFire_between gc (right t) a1.val phase.s.val
        ha1_le_s phase.s.isLt hnoR).symm⟩
private theorem left_ne_self_nfec (t : Fin sys.rs.n) : left t ≠ t := by
  intro hEq
  have hval := congrArg Fin.val hEq
  simp only [left_val] at hval
  have ht := t.isLt
  have hn := sys.rs.n_ge_4
  by_cases h0 : t.val = 0
  · rw [h0] at hval
    simp only [Nat.zero_add] at hval
    rw [Nat.mod_eq_of_lt (show sys.rs.n - 1 < sys.rs.n by omega)] at hval
    omega
  · rw [show t.val + sys.rs.n - 1 = (t.val - 1) + sys.rs.n from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (show t.val - 1 < sys.rs.n by omega)] at hval
    omega

private theorem right_ne_self_nfec (t : Fin sys.rs.n) : right t ≠ t := by
  intro hEq
  have hval := congrArg Fin.val hEq
  simp only [right_val] at hval
  have ht := t.isLt
  have hn := sys.rs.n_ge_4
  by_cases h1 : t.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt h1] at hval
    omega
  · rw [show t.val + 1 = sys.rs.n from by omega, Nat.mod_self] at hval
    omega

/-- Local binary dichotomy helper copied into `NormalFormEC` so the cyclic wrap
    helpers do not depend on private lemmas from `TernaryPhaseEC`. -/
private theorem fin_binary_dichotomy_nfec {n : Nat} (hn : n = 2)
    (a b : Fin n) (hab : a ≠ b) (c : Fin n) : c = a ∨ c = b := by
  subst hn
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  interval_cases a.val <;> interval_cases b.val <;> interval_cases c.val
    <;> simp_all [Fin.ext_iff] <;> omega

/-- If the head part `[0, s_min)` of the cyclic wrap already contains at least
    two `left t` fires and no `right t` fires, then the wrap yields EC by the
    usual Toggle-FR mechanism with mover step `s_min`. -/
private theorem wrap_head_toggleFR_left_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min : Fin gc.configs.length)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hheadL_ge2 : 2 ≤ gc.intervalFireCount (left t) 0 s_min.val)
    (hheadR0 : gc.intervalFireCount (right t) 0 s_min.val = 0) :
    hasEntryConflict gc := by
  have hs_min_pos : 0 < s_min.val := by
    by_contra h
    have hs0 : s_min.val = 0 := by omega
    rw [hs0] at hheadL_ge2
    simp [GoodCycle.intervalFireCount] at hheadL_ge2
  have hex1 : ∃ k : Fin gc.configs.length,
      0 ≤ k.val ∧ k.val < s_min.val ∧ gc.moverAt k = left t := by
    by_contra hnone
    have hzero : gc.intervalFireCount (left t) 0 s_min.val = 0 := by
      exact intervalFireCount_eq_zero_of_noFire gc (left t) (Nat.zero_le _) (Nat.le_of_lt s_min.isLt)
        (fun k _ hk2 hkm => hnone ⟨k, Nat.zero_le _, hk2, hkm⟩)
    omega
  obtain ⟨a1, _, ha1_lt_s, ha1_left, ha1_first⟩ :=
    exists_first_fire gc (left t) 0 s_min.val hex1
  have ha1_nonmover_t : gc.moverAt a1 ≠ t := by
    rw [ha1_left]
    exact left_ne_self_nfec t
  have hbefore0 : gc.intervalFireCount (left t) 0 a1.val = 0 := by
    exact intervalFireCount_eq_zero_of_noFire gc (left t) (Nat.zero_le _) (Nat.le_of_lt a1.isLt)
      (fun k _ hk2 => ha1_first k (Nat.zero_le _) hk2)
  have hsingle1 : gc.intervalFireCount (left t) a1.val (a1.val + 1) = 1 := by
    rw [intervalFireCount_single gc (left t) a1.isLt]
    simp [ha1_left]
  have hsplit1 := intervalFireCount_split gc (left t) (Nat.zero_le a1.val)
    (show a1.val ≤ a1.val + 1 by omega)
  have hsplit2 := intervalFireCount_split gc (left t) (Nat.zero_le (a1.val + 1))
    (show a1.val + 1 ≤ s_min.val by omega)
  have htail_ge1 : 1 ≤ gc.intervalFireCount (left t) (a1.val + 1) s_min.val := by
    omega
  have hex2 : ∃ k : Fin gc.configs.length,
      a1.val + 1 ≤ k.val ∧ k.val < s_min.val ∧ gc.moverAt k = left t := by
    by_contra hnone
    have hzero_tail : gc.intervalFireCount (left t) (a1.val + 1) s_min.val = 0 := by
      exact intervalFireCount_eq_zero_of_noFire gc (left t) (by omega) (Nat.le_of_lt s_min.isLt)
        (fun k hk1 hk2 hkm => hnone ⟨k, hk1, hk2, hkm⟩)
    omega
  obtain ⟨a2, ha2_ge, ha2_lt_s, ha2_left, ha2_first⟩ :=
    exists_first_fire gc (left t) (a1.val + 1) s_min.val hex2
  have ha1_lt_a2 : a1.val < a2.val := by
    omega
  have ha2_nonmover_t : gc.moverAt a2 ≠ t := by
    rw [ha2_left]
    exact left_ne_self_nfec t
  have ha1succ_lt : a1.val + 1 < gc.configs.length := by
    omega
  let a1succ : Fin gc.configs.length := ⟨a1.val + 1, ha1succ_lt⟩
  have ha1_next : nextIndex gc.configs a1 = a1succ := by
    apply Fin.ext
    simp [nextIndex, a1succ, Nat.mod_eq_of_lt ha1succ_lt]
  have hdiff_step :
      (gc.configs.get a1succ) (left t) ≠ (gc.configs.get a1) (left t) := by
    have hstep := gc.state_ne_at_moverAt a1
    rw [ha1_next, ha1_left] at hstep
    exact hstep
  have hconst_left :
      (gc.configs.get a1succ) (left t) = (gc.configs.get a2) (left t) := by
    exact configVal_eq_of_noFire_between gc (left t) (a1.val + 1) a2.val
      (by omega) a2.isLt
      (fun k hk1 hk2 => ha2_first k hk1 hk2)
  have hL_diff :
      (gc.configs.get a1) (left t) ≠ (gc.configs.get a2) (left t) := by
    intro hEq
    exact hdiff_step (hconst_left.trans hEq.symm)
  have ht_nofire_from_a1 :
      ∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < s_min.val → gc.moverAt k ≠ t := by
    intro k hk1 hk2
    exact hno_t_before k hk2
  have hR_nofire_from_a1 :
      ∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < s_min.val → gc.moverAt k ≠ right t := by
    intro k hk1 hk2
    exact noFire_of_ifc_zero gc (right t) (Nat.le_of_lt s_min.isLt) hheadR0
      k (by omega) hk2
  exact toggleFR_ec gc t a1 a2 s_min ha1_lt_a2 ha2_lt_s
    hs_min_fire ha1_nonmover_t ha2_nonmover_t ht_nofire_from_a1
    hbL hbR hR_nofire_from_a1 hL_diff

/-- If the tail part `[(s_max+1), CL)` of the cyclic wrap contains at least two
    `left t` fires and the whole wrap has no `right t` fires, then the wrap
    yields EC by a cyclic Toggle-FR argument ending at the mover step `s_min`. -/
private theorem wrap_tail_toggleFR_left_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (htailL_ge2 : 2 ≤ gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length)
    (hwrapR0 : gc.intervalFireCount (right t) 0 s_min.val +
      gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length = 0) :
    hasEntryConflict gc := by
  have hs1_lt : s_max.val + 1 < gc.configs.length := by
    by_contra h
    have hlast : s_max.val + 1 = gc.configs.length := by omega
    rw [hlast] at htailL_ge2
    simp [GoodCycle.intervalFireCount] at htailL_ge2
  have hheadR0 : gc.intervalFireCount (right t) 0 s_min.val = 0 := by
    omega
  have htailR0 : gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length = 0 := by
    omega
  have hex1 : ∃ k : Fin gc.configs.length,
      s_max.val + 1 ≤ k.val ∧ k.val < gc.configs.length ∧ gc.moverAt k = left t := by
    by_contra hnone
    have hzero : gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length = 0 := by
      exact intervalFireCount_eq_zero_of_noFire gc (left t) (by omega) le_rfl
        (fun k hk1 hk2 hkm => hnone ⟨k, hk1, hk2, hkm⟩)
    omega
  obtain ⟨a1, ha1_ge, _ha1_lt_len, ha1_left, ha1_first⟩ :=
    exists_first_fire gc (left t) (s_max.val + 1) gc.configs.length hex1
  have ha1_nonmover_t : gc.moverAt a1 ≠ t := by
    rw [ha1_left]
    exact left_ne_self_nfec t
  have hbefore_tail0 : gc.intervalFireCount (left t) (s_max.val + 1) a1.val = 0 := by
    exact intervalFireCount_eq_zero_of_noFire gc (left t) (by omega) (Nat.le_of_lt a1.isLt)
      (fun k hk1 hk2 => ha1_first k hk1 hk2)
  have hsingle1 : gc.intervalFireCount (left t) a1.val (a1.val + 1) = 1 := by
    rw [intervalFireCount_single gc (left t) a1.isLt]
    simp [ha1_left]
  have hsplit1 := intervalFireCount_split gc (left t) (show s_max.val + 1 ≤ a1.val by omega)
    (show a1.val ≤ a1.val + 1 by omega)
  have hsplit2 := intervalFireCount_split gc (left t) (show s_max.val + 1 ≤ a1.val + 1 by omega)
    (show a1.val + 1 ≤ gc.configs.length by omega)
  have htail_ge1 : 1 ≤ gc.intervalFireCount (left t) (a1.val + 1) gc.configs.length := by
    omega
  have hex2 : ∃ k : Fin gc.configs.length,
      a1.val + 1 ≤ k.val ∧ k.val < gc.configs.length ∧ gc.moverAt k = left t := by
    by_contra hnone
    have hzero_tail : gc.intervalFireCount (left t) (a1.val + 1) gc.configs.length = 0 := by
      exact intervalFireCount_eq_zero_of_noFire gc (left t) (by omega) le_rfl
        (fun k hk1 hk2 hkm => hnone ⟨k, hk1, hk2, hkm⟩)
    omega
  obtain ⟨a2, ha2_ge, _ha2_lt_len, ha2_left, ha2_first⟩ :=
    exists_first_fire gc (left t) (a1.val + 1) gc.configs.length hex2
  have ha1_lt_a2 : a1.val < a2.val := by
    omega
  have ha2_nonmover_t : gc.moverAt a2 ≠ t := by
    rw [ha2_left]
    exact left_ne_self_nfec t
  have ha1succ_lt : a1.val + 1 < gc.configs.length := by
    omega
  let a1succ : Fin gc.configs.length := ⟨a1.val + 1, ha1succ_lt⟩
  have ha1_next : nextIndex gc.configs a1 = a1succ := by
    apply Fin.ext
    simp [nextIndex, a1succ, Nat.mod_eq_of_lt ha1succ_lt]
  have hdiff_step :
      (gc.configs.get a1succ) (left t) ≠ (gc.configs.get a1) (left t) := by
    have hstep := gc.state_ne_at_moverAt a1
    rw [ha1_next, ha1_left] at hstep
    exact hstep
  have hconst_left :
      (gc.configs.get a1succ) (left t) = (gc.configs.get a2) (left t) := by
    exact configVal_eq_of_noFire_between gc (left t) (a1.val + 1) a2.val
      (by omega) a2.isLt
      (fun k hk1 hk2 => ha2_first k hk1 hk2)
  have hL_diff :
      (gc.configs.get a1) (left t) ≠ (gc.configs.get a2) (left t) := by
    intro hEq
    exact hdiff_step (hconst_left.trans hEq.symm)
  have hctx_t_a1 :
      (gc.configs.get a1) t = (gc.configs.get s_min) t := by
    exact configVal_eq_of_cyclic_noFire gc t s_min.val a1.val
      s_min.isLt a1.isLt (by omega)
      (fun k hk_ge => hno_t_after k (by omega))
      (fun k hk_lt => hno_t_before k hk_lt)
  have hctx_t_a2 :
      (gc.configs.get a2) t = (gc.configs.get s_min) t := by
    exact configVal_eq_of_cyclic_noFire gc t s_min.val a2.val
      s_min.isLt a2.isLt (by omega)
      (fun k hk_ge => hno_t_after k (by omega))
      (fun k hk_lt => hno_t_before k hk_lt)
  have hR_nofire_tail :
      ∀ k : Fin gc.configs.length, a1.val ≤ k.val → gc.moverAt k ≠ right t := by
    intro k hk_ge
    exact noFire_of_ifc_zero gc (right t) le_rfl htailR0
      k (by omega) k.isLt
  have hR_nofire_head :
      ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ right t := by
    intro k hk_lt
    exact noFire_of_ifc_zero gc (right t) (Nat.le_of_lt s_min.isLt) hheadR0
      k (Nat.zero_le _) hk_lt
  have hctx_R_a1 :
      (gc.configs.get a1) (right t) = (gc.configs.get s_min) (right t) := by
    exact configVal_eq_of_cyclic_noFire gc (right t) s_min.val a1.val
      s_min.isLt a1.isLt (by omega)
      (fun k hk_ge => hR_nofire_tail k hk_ge)
      (fun k hk_lt => hR_nofire_head k hk_lt)
  have hctx_R_a2 :
      (gc.configs.get a2) (right t) = (gc.configs.get s_min) (right t) := by
    exact configVal_eq_of_cyclic_noFire gc (right t) s_min.val a2.val
      s_min.isLt a2.isLt (by omega)
      (fun k hk_ge => hR_nofire_tail k (by omega))
      (fun k hk_lt => hR_nofire_head k hk_lt)
  have hL_dichotomy :
      (gc.configs.get s_min) (left t) = (gc.configs.get a1) (left t) ∨
      (gc.configs.get s_min) (left t) = (gc.configs.get a2) (left t) := by
    exact fin_binary_dichotomy_nfec hbL
      ((gc.configs.get a1) (left t)) ((gc.configs.get a2) (left t))
      hL_diff ((gc.configs.get s_min) (left t))
  rcases hL_dichotomy with hL_eq_a1 | hL_eq_a2
  · exact ⟨s_min, a1, t, hs_min_fire, ha1_nonmover_t,
      hL_eq_a1, hctx_t_a1.symm, hctx_R_a1.symm⟩
  · exact ⟨s_min, a2, t, hs_min_fire, ha2_nonmover_t,
      hL_eq_a2, hctx_t_a2.symm, hctx_R_a2.symm⟩

/-- The cyclic wrap cannot be left-one-sided with odd contribution at least `2`:
    such a wrap has at least two `left t` fires either in the head or in the
    tail segment, and each segment already yields Toggle-FR EC. -/
private theorem cyclic_wrap_left_odd_one_sided_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (hwrapL_odd :
      Odd (gc.intervalFireCount (left t) 0 s_min.val +
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length))
    (hwrapL_ge2 :
      2 ≤ gc.intervalFireCount (left t) 0 s_min.val +
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length)
    (hwrapR0 :
      gc.intervalFireCount (right t) 0 s_min.val +
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length = 0) :
    hasEntryConflict gc := by
  let headL := gc.intervalFireCount (left t) 0 s_min.val
  let tailL := gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length
  have hhead_or_tail :
      2 ≤ headL ∨ 2 ≤ tailL := by
    by_cases hhead : 2 ≤ headL
    · exact Or.inl hhead
    · right
      have hhead_le1 : headL ≤ 1 := by omega
      have htail_ge2 : 2 ≤ tailL := by
        obtain ⟨m, hm⟩ := hwrapL_odd
        dsimp [headL, tailL] at hm ⊢
        omega
      exact htail_ge2
  rcases hhead_or_tail with hhead_ge2 | htail_ge2
  · have hheadR0 : gc.intervalFireCount (right t) 0 s_min.val = 0 := by
      omega
    exact wrap_head_toggleFR_left_ec gc t hbL hbR s_min hs_min_fire
      hno_t_before hhead_ge2 hheadR0
  · exact wrap_tail_toggleFR_left_ec gc t hbL hbR s_min s_max hs_lt hs_min_fire
      hno_t_before hno_t_after htail_ge2 hwrapR0

/-- Symmetric head-side Toggle-FR helper for the cyclic wrap. -/
private theorem wrap_head_toggleFR_right_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min : Fin gc.configs.length)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hheadR_ge2 : 2 ≤ gc.intervalFireCount (right t) 0 s_min.val)
    (hheadL0 : gc.intervalFireCount (left t) 0 s_min.val = 0) :
    hasEntryConflict gc := by
  have hs_min_pos : 0 < s_min.val := by
    by_contra h
    have hs0 : s_min.val = 0 := by omega
    rw [hs0] at hheadR_ge2
    simp [GoodCycle.intervalFireCount] at hheadR_ge2
  have hex1 : ∃ k : Fin gc.configs.length,
      0 ≤ k.val ∧ k.val < s_min.val ∧ gc.moverAt k = right t := by
    by_contra hnone
    have hzero : gc.intervalFireCount (right t) 0 s_min.val = 0 := by
      exact intervalFireCount_eq_zero_of_noFire gc (right t) (Nat.zero_le _) (Nat.le_of_lt s_min.isLt)
        (fun k _ hk2 hkm => hnone ⟨k, Nat.zero_le _, hk2, hkm⟩)
    omega
  obtain ⟨a1, _, ha1_lt_s, ha1_right, ha1_first⟩ :=
    exists_first_fire gc (right t) 0 s_min.val hex1
  have ha1_nonmover_t : gc.moverAt a1 ≠ t := by
    rw [ha1_right]
    exact right_ne_self_nfec t
  have hbefore0 : gc.intervalFireCount (right t) 0 a1.val = 0 := by
    exact intervalFireCount_eq_zero_of_noFire gc (right t) (Nat.zero_le _) (Nat.le_of_lt a1.isLt)
      (fun k _ hk2 => ha1_first k (Nat.zero_le _) hk2)
  have hsingle1 : gc.intervalFireCount (right t) a1.val (a1.val + 1) = 1 := by
    rw [intervalFireCount_single gc (right t) a1.isLt]
    simp [ha1_right]
  have hsplit1 := intervalFireCount_split gc (right t) (Nat.zero_le a1.val)
    (show a1.val ≤ a1.val + 1 by omega)
  have hsplit2 := intervalFireCount_split gc (right t) (Nat.zero_le (a1.val + 1))
    (show a1.val + 1 ≤ s_min.val by omega)
  have htail_ge1 : 1 ≤ gc.intervalFireCount (right t) (a1.val + 1) s_min.val := by
    omega
  have hex2 : ∃ k : Fin gc.configs.length,
      a1.val + 1 ≤ k.val ∧ k.val < s_min.val ∧ gc.moverAt k = right t := by
    by_contra hnone
    have hzero_tail : gc.intervalFireCount (right t) (a1.val + 1) s_min.val = 0 := by
      exact intervalFireCount_eq_zero_of_noFire gc (right t) (by omega) (Nat.le_of_lt s_min.isLt)
        (fun k hk1 hk2 hkm => hnone ⟨k, hk1, hk2, hkm⟩)
    omega
  obtain ⟨a2, ha2_ge, ha2_lt_s, ha2_right, ha2_first⟩ :=
    exists_first_fire gc (right t) (a1.val + 1) s_min.val hex2
  have ha1_lt_a2 : a1.val < a2.val := by
    omega
  have ha2_nonmover_t : gc.moverAt a2 ≠ t := by
    rw [ha2_right]
    exact right_ne_self_nfec t
  have ha1succ_lt : a1.val + 1 < gc.configs.length := by
    omega
  let a1succ : Fin gc.configs.length := ⟨a1.val + 1, ha1succ_lt⟩
  have ha1_next : nextIndex gc.configs a1 = a1succ := by
    apply Fin.ext
    simp [nextIndex, a1succ, Nat.mod_eq_of_lt ha1succ_lt]
  have hdiff_step :
      (gc.configs.get a1succ) (right t) ≠ (gc.configs.get a1) (right t) := by
    have hstep := gc.state_ne_at_moverAt a1
    rw [ha1_next, ha1_right] at hstep
    exact hstep
  have hconst_right :
      (gc.configs.get a1succ) (right t) = (gc.configs.get a2) (right t) := by
    exact configVal_eq_of_noFire_between gc (right t) (a1.val + 1) a2.val
      (by omega) a2.isLt
      (fun k hk1 hk2 => ha2_first k hk1 hk2)
  have hR_diff :
      (gc.configs.get a1) (right t) ≠ (gc.configs.get a2) (right t) := by
    intro hEq
    exact hdiff_step (hconst_right.trans hEq.symm)
  have ht_nofire_from_a1 :
      ∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < s_min.val → gc.moverAt k ≠ t := by
    intro k hk1 hk2
    exact hno_t_before k hk2
  have hL_nofire_from_a1 :
      ∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < s_min.val → gc.moverAt k ≠ left t := by
    intro k hk1 hk2
    exact noFire_of_ifc_zero gc (left t) (Nat.le_of_lt s_min.isLt) hheadL0
      k (by omega) hk2
  exact toggleFR_ec_symm gc t a1 a2 s_min ha1_lt_a2 ha2_lt_s
    hs_min_fire ha1_nonmover_t ha2_nonmover_t ht_nofire_from_a1
    hbL hbR hL_nofire_from_a1 hR_diff

/-- Symmetric tail-side cyclic Toggle-FR helper for the wrap. -/
private theorem wrap_tail_toggleFR_right_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (htailR_ge2 : 2 ≤ gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length)
    (hwrapL0 : gc.intervalFireCount (left t) 0 s_min.val +
      gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length = 0) :
    hasEntryConflict gc := by
  have hs1_lt : s_max.val + 1 < gc.configs.length := by
    by_contra h
    have hlast : s_max.val + 1 = gc.configs.length := by omega
    rw [hlast] at htailR_ge2
    simp [GoodCycle.intervalFireCount] at htailR_ge2
  have hheadL0 : gc.intervalFireCount (left t) 0 s_min.val = 0 := by
    omega
  have htailL0 : gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length = 0 := by
    omega
  have hex1 : ∃ k : Fin gc.configs.length,
      s_max.val + 1 ≤ k.val ∧ k.val < gc.configs.length ∧ gc.moverAt k = right t := by
    by_contra hnone
    have hzero : gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length = 0 := by
      exact intervalFireCount_eq_zero_of_noFire gc (right t) (by omega) le_rfl
        (fun k hk1 hk2 hkm => hnone ⟨k, hk1, hk2, hkm⟩)
    omega
  obtain ⟨a1, ha1_ge, _ha1_lt_len, ha1_right, ha1_first⟩ :=
    exists_first_fire gc (right t) (s_max.val + 1) gc.configs.length hex1
  have ha1_nonmover_t : gc.moverAt a1 ≠ t := by
    rw [ha1_right]
    exact right_ne_self_nfec t
  have hbefore_tail0 : gc.intervalFireCount (right t) (s_max.val + 1) a1.val = 0 := by
    exact intervalFireCount_eq_zero_of_noFire gc (right t) (by omega) (Nat.le_of_lt a1.isLt)
      (fun k hk1 hk2 => ha1_first k hk1 hk2)
  have hsingle1 : gc.intervalFireCount (right t) a1.val (a1.val + 1) = 1 := by
    rw [intervalFireCount_single gc (right t) a1.isLt]
    simp [ha1_right]
  have hsplit1 := intervalFireCount_split gc (right t) (show s_max.val + 1 ≤ a1.val by omega)
    (show a1.val ≤ a1.val + 1 by omega)
  have hsplit2 := intervalFireCount_split gc (right t) (show s_max.val + 1 ≤ a1.val + 1 by omega)
    (show a1.val + 1 ≤ gc.configs.length by omega)
  have htail_ge1 : 1 ≤ gc.intervalFireCount (right t) (a1.val + 1) gc.configs.length := by
    omega
  have hex2 : ∃ k : Fin gc.configs.length,
      a1.val + 1 ≤ k.val ∧ k.val < gc.configs.length ∧ gc.moverAt k = right t := by
    by_contra hnone
    have hzero_tail : gc.intervalFireCount (right t) (a1.val + 1) gc.configs.length = 0 := by
      exact intervalFireCount_eq_zero_of_noFire gc (right t) (by omega) le_rfl
        (fun k hk1 hk2 hkm => hnone ⟨k, hk1, hk2, hkm⟩)
    omega
  obtain ⟨a2, ha2_ge, _ha2_lt_len, ha2_right, ha2_first⟩ :=
    exists_first_fire gc (right t) (a1.val + 1) gc.configs.length hex2
  have ha1_lt_a2 : a1.val < a2.val := by
    omega
  have ha2_nonmover_t : gc.moverAt a2 ≠ t := by
    rw [ha2_right]
    exact right_ne_self_nfec t
  have ha1succ_lt : a1.val + 1 < gc.configs.length := by
    omega
  let a1succ : Fin gc.configs.length := ⟨a1.val + 1, ha1succ_lt⟩
  have ha1_next : nextIndex gc.configs a1 = a1succ := by
    apply Fin.ext
    simp [nextIndex, a1succ, Nat.mod_eq_of_lt ha1succ_lt]
  have hdiff_step :
      (gc.configs.get a1succ) (right t) ≠ (gc.configs.get a1) (right t) := by
    have hstep := gc.state_ne_at_moverAt a1
    rw [ha1_next, ha1_right] at hstep
    exact hstep
  have hconst_right :
      (gc.configs.get a1succ) (right t) = (gc.configs.get a2) (right t) := by
    exact configVal_eq_of_noFire_between gc (right t) (a1.val + 1) a2.val
      (by omega) a2.isLt
      (fun k hk1 hk2 => ha2_first k hk1 hk2)
  have hR_diff :
      (gc.configs.get a1) (right t) ≠ (gc.configs.get a2) (right t) := by
    intro hEq
    exact hdiff_step (hconst_right.trans hEq.symm)
  have hctx_t_a1 :
      (gc.configs.get a1) t = (gc.configs.get s_min) t := by
    exact configVal_eq_of_cyclic_noFire gc t s_min.val a1.val
      s_min.isLt a1.isLt (by omega)
      (fun k hk_ge => hno_t_after k (by omega))
      (fun k hk_lt => hno_t_before k hk_lt)
  have hctx_t_a2 :
      (gc.configs.get a2) t = (gc.configs.get s_min) t := by
    exact configVal_eq_of_cyclic_noFire gc t s_min.val a2.val
      s_min.isLt a2.isLt (by omega)
      (fun k hk_ge => hno_t_after k (by omega))
      (fun k hk_lt => hno_t_before k hk_lt)
  have hL_nofire_tail :
      ∀ k : Fin gc.configs.length, a1.val ≤ k.val → gc.moverAt k ≠ left t := by
    intro k hk_ge
    exact noFire_of_ifc_zero gc (left t) le_rfl htailL0
      k (by omega) k.isLt
  have hL_nofire_head :
      ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ left t := by
    intro k hk_lt
    exact noFire_of_ifc_zero gc (left t) (Nat.le_of_lt s_min.isLt) hheadL0
      k (Nat.zero_le _) hk_lt
  have hctx_L_a1 :
      (gc.configs.get a1) (left t) = (gc.configs.get s_min) (left t) := by
    exact configVal_eq_of_cyclic_noFire gc (left t) s_min.val a1.val
      s_min.isLt a1.isLt (by omega)
      (fun k hk_ge => hL_nofire_tail k hk_ge)
      (fun k hk_lt => hL_nofire_head k hk_lt)
  have hctx_L_a2 :
      (gc.configs.get a2) (left t) = (gc.configs.get s_min) (left t) := by
    exact configVal_eq_of_cyclic_noFire gc (left t) s_min.val a2.val
      s_min.isLt a2.isLt (by omega)
      (fun k hk_ge => hL_nofire_tail k (by omega))
      (fun k hk_lt => hL_nofire_head k hk_lt)
  have hR_dichotomy :
      (gc.configs.get s_min) (right t) = (gc.configs.get a1) (right t) ∨
      (gc.configs.get s_min) (right t) = (gc.configs.get a2) (right t) := by
    exact fin_binary_dichotomy_nfec hbR
      ((gc.configs.get a1) (right t)) ((gc.configs.get a2) (right t))
      hR_diff ((gc.configs.get s_min) (right t))
  rcases hR_dichotomy with hR_eq_a1 | hR_eq_a2
  · exact ⟨s_min, a1, t, hs_min_fire, ha1_nonmover_t,
      hctx_L_a1.symm, hctx_t_a1.symm, hR_eq_a1⟩
  · exact ⟨s_min, a2, t, hs_min_fire, ha2_nonmover_t,
      hctx_L_a2.symm, hctx_t_a2.symm, hR_eq_a2⟩

/-- Symmetric odd one-sided wrap reduction on the right side. -/
private theorem cyclic_wrap_right_odd_one_sided_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (hwrapR_odd :
      Odd (gc.intervalFireCount (right t) 0 s_min.val +
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length))
    (hwrapR_ge2 :
      2 ≤ gc.intervalFireCount (right t) 0 s_min.val +
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length)
    (hwrapL0 :
      gc.intervalFireCount (left t) 0 s_min.val +
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length = 0) :
    hasEntryConflict gc := by
  let headR := gc.intervalFireCount (right t) 0 s_min.val
  let tailR := gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length
  have hhead_or_tail :
      2 ≤ headR ∨ 2 ≤ tailR := by
    by_cases hhead : 2 ≤ headR
    · exact Or.inl hhead
    · right
      have hhead_le1 : headR ≤ 1 := by omega
      have htail_ge2 : 2 ≤ tailR := by
        obtain ⟨m, hm⟩ := hwrapR_odd
        dsimp [headR, tailR] at hm ⊢
        omega
      exact htail_ge2
  rcases hhead_or_tail with hhead_ge2 | htail_ge2
  · have hheadL0 : gc.intervalFireCount (left t) 0 s_min.val = 0 := by
      omega
    exact wrap_head_toggleFR_right_ec gc t hbL hbR s_min hs_min_fire
      hno_t_before hhead_ge2 hheadL0
  · exact wrap_tail_toggleFR_right_ec gc t hbL hbR s_min s_max hs_lt hs_min_fire
      hno_t_before hno_t_after htail_ge2 hwrapL0

/-- After the cyclic both-even and odd one-sided wrap cases are removed, any
    positive wrap contribution `≥ 2` must already be genuinely mixed. -/
private theorem cyclic_wrap_ge2_mixed_reduction
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (hnoEC : ¬hasEntryConflict gc)
    (hwrap_ge2 :
      2 ≤
        (gc.intervalFireCount (left t) 0 s_min.val +
          gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length) +
        (gc.intervalFireCount (right t) 0 s_min.val +
          gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length)) :
    1 ≤ gc.intervalFireCount (left t) 0 s_min.val +
          gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length ∧
      1 ≤ gc.intervalFireCount (right t) 0 s_min.val +
          gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length ∧
      (Odd (gc.intervalFireCount (left t) 0 s_min.val +
          gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length) ∨
        Odd (gc.intervalFireCount (right t) 0 s_min.val +
          gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length)) := by
  rcases cyclic_wrap_ge2_reduction gc t hbL hbR s_min s_max hs_lt hs_min_fire
      hno_t_before hno_t_after hnoEC hwrap_ge2 with hleft | hright | hmixed
  · exfalso
    exact entryConflict_impossible gc
      (cyclic_wrap_left_odd_one_sided_ec gc t hbL hbR s_min s_max hs_lt hs_min_fire
        hno_t_before hno_t_after hleft.1 (by
          omega) hleft.2)
  · exfalso
    exact entryConflict_impossible gc
      (cyclic_wrap_right_odd_one_sided_ec gc t hbL hbR s_min s_max hs_lt hs_min_fire
        hno_t_before hno_t_after hright.2 (by
          omega) hright.1)
  · exact hmixed

/-- If a cyclic mixed-wrap contribution already sits entirely in the head
    interval `[0, s_min)`, choose the earliest head fire of either binary
    neighbor as the phase start. The remainder of the head is then a linear
    mixed phase ending at `s_min`, so the existing `mixed_phase_ec` closes it. -/
private theorem wrap_head_mixed_ec
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min : Fin gc.configs.length)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hheadL_pos : 1 ≤ gc.intervalFireCount (left t) 0 s_min.val)
    (hheadR_pos : 1 ≤ gc.intervalFireCount (right t) 0 s_min.val) :
    hasEntryConflict gc := by
  have hs_min_pos : 0 < s_min.val := by
    by_contra h
    have hs0 : s_min.val = 0 := by omega
    rw [hs0] at hheadL_pos
    simp [GoodCycle.intervalFireCount] at hheadL_pos
  obtain ⟨fL, h0fL, hfL_lt, hfL_mover, hfL_first⟩ :=
    exists_first_fire gc (left t) 0 s_min.val
      (exists_fire_step_in_interval gc (left t) (Nat.zero_le _) (Nat.le_of_lt s_min.isLt) hheadL_pos)
  obtain ⟨fR, h0fR, hfR_lt, hfR_mover, hfR_first⟩ :=
    exists_first_fire gc (right t) 0 s_min.val
      (exists_fire_step_in_interval gc (right t) (Nat.zero_le _) (Nat.le_of_lt s_min.isLt) hheadR_pos)
  by_cases hLR : fL.val ≤ fR.val
  · have hfL_lt_fR : fL.val < fR.val := by
      by_cases hEq : fL.val = fR.val
      · have hFin : fL = fR := Fin.ext hEq
        have hEqLR : left t = right t := by
          calc
            left t = gc.moverAt fR := by simpa [hFin] using hfL_mover.symm
            _ = right t := hfR_mover
        exact False.elim (left_ne_right (by omega) t hEqLR)
      · omega
    have hfL_nonmover : gc.moverAt fL ≠ t := by
      rw [hfL_mover]
      exact left_ne_self_nfec t
    let phase : TernaryPhase gc t :=
      { a := fL
        s := s_min
        ha_lt_s := hfL_lt
        hs_mover := hs_min_fire
        ha_nonmover := hfL_nonmover
        ht_nofire := by
          intro k hk1 hk2
          exact hno_t_before k hk2 }
    have hJ_pos :
        gc.intervalFireCount (left t) phase.a.val phase.s.val ≥ 1 := by
      have hone : gc.intervalFireCount (left t) fL.val (fL.val + 1) = 1 := by
        rw [intervalFireCount_single gc (left t) fL.isLt]
        simp [hfL_mover]
      have hsplit := intervalFireCount_split gc (left t)
        (show fL.val ≤ fL.val + 1 by omega)
        (show fL.val + 1 ≤ s_min.val by omega)
      simpa [phase] using (show 1 ≤ gc.intervalFireCount (left t) fL.val s_min.val by omega)
    have hK_pos :
        gc.intervalFireCount (right t) phase.a.val phase.s.val ≥ 1 := by
      have hone : gc.intervalFireCount (right t) fR.val (fR.val + 1) = 1 := by
        rw [intervalFireCount_single gc (right t) fR.isLt]
        simp [hfR_mover]
      have hsplit1 := intervalFireCount_split gc (right t)
        (show fL.val ≤ fR.val by omega)
        (show fR.val ≤ fR.val + 1 by omega)
      have hsplit2 := intervalFireCount_split gc (right t)
        (show fL.val ≤ fR.val + 1 by omega)
        (show fR.val + 1 ≤ s_min.val by omega)
      simpa [phase] using (show 1 ≤ gc.intervalFireCount (right t) fL.val s_min.val by omega)
    exact mixed_phase_ec gc hn t hbL hbR phase (by simpa [phase] using Or.inl hfL_mover) hJ_pos hK_pos
  · have hfR_lt_fL : fR.val < fL.val := by omega
    have hfR_nonmover : gc.moverAt fR ≠ t := by
      rw [hfR_mover]
      exact right_ne_self_nfec t
    let phase : TernaryPhase gc t :=
      { a := fR
        s := s_min
        ha_lt_s := hfR_lt
        hs_mover := hs_min_fire
        ha_nonmover := hfR_nonmover
        ht_nofire := by
          intro k hk1 hk2
          exact hno_t_before k hk2 }
    have hJ_pos :
        gc.intervalFireCount (left t) phase.a.val phase.s.val ≥ 1 := by
      have hone : gc.intervalFireCount (left t) fL.val (fL.val + 1) = 1 := by
        rw [intervalFireCount_single gc (left t) fL.isLt]
        simp [hfL_mover]
      have hsplit1 := intervalFireCount_split gc (left t)
        (show fR.val ≤ fL.val by omega)
        (show fL.val ≤ fL.val + 1 by omega)
      have hsplit2 := intervalFireCount_split gc (left t)
        (show fR.val ≤ fL.val + 1 by omega)
        (show fL.val + 1 ≤ s_min.val by omega)
      simpa [phase] using (show 1 ≤ gc.intervalFireCount (left t) fR.val s_min.val by omega)
    have hK_pos :
        gc.intervalFireCount (right t) phase.a.val phase.s.val ≥ 1 := by
      have hone : gc.intervalFireCount (right t) fR.val (fR.val + 1) = 1 := by
        rw [intervalFireCount_single gc (right t) fR.isLt]
        simp [hfR_mover]
      have hsplit := intervalFireCount_split gc (right t)
        (show fR.val ≤ fR.val + 1 by omega)
        (show fR.val + 1 ≤ s_min.val by omega)
      simpa [phase] using (show 1 ≤ gc.intervalFireCount (right t) fR.val s_min.val by omega)
    exact mixed_phase_ec gc hn t hbL hbR phase (by simpa [phase] using Or.inr hfR_mover) hJ_pos hK_pos

/-- Under `¬EC`, a positive wrap contribution reduced to the mixed case cannot
    already be mixed in the head segment. So any surviving mixed wrap is either
    mixed in the tail segment or is a pure cross-boundary split:
    left-only in the head and right-only in the tail, or vice versa. -/
private theorem cyclic_wrap_mixed_shape_reduction
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (hnoEC : ¬hasEntryConflict gc)
    (hwrap_ge2 :
      2 ≤
        (gc.intervalFireCount (left t) 0 s_min.val +
          gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length) +
        (gc.intervalFireCount (right t) 0 s_min.val +
          gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length)) :
    (1 ≤ gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length ∧
      1 ≤ gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length) ∨
    (1 ≤ gc.intervalFireCount (left t) 0 s_min.val ∧
      gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length = 0 ∧
      gc.intervalFireCount (right t) 0 s_min.val = 0 ∧
      1 ≤ gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length) ∨
    (gc.intervalFireCount (left t) 0 s_min.val = 0 ∧
      1 ≤ gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length ∧
      1 ≤ gc.intervalFireCount (right t) 0 s_min.val ∧
      gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length = 0) := by
  let headL := gc.intervalFireCount (left t) 0 s_min.val
  let tailL := gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length
  let headR := gc.intervalFireCount (right t) 0 s_min.val
  let tailR := gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length
  have hmixed := cyclic_wrap_ge2_mixed_reduction gc t hbL hbR s_min s_max hs_lt hs_min_fire
    hno_t_before hno_t_after hnoEC hwrap_ge2
  have hL_pos : 1 ≤ headL + tailL := by
    simpa [headL, tailL] using hmixed.1
  have hR_pos : 1 ≤ headR + tailR := by
    simpa [headR, tailR] using hmixed.2.1
  by_cases hheadMixed : 1 ≤ headL ∧ 1 ≤ headR
  · exfalso
    exact hnoEC (wrap_head_mixed_ec gc hn t hbL hbR s_min hs_min_fire
      hno_t_before hheadMixed.1 hheadMixed.2)
  · by_cases htailMixed : 1 ≤ tailL ∧ 1 ≤ tailR
    · exact Or.inl htailMixed
    · have hshape :
          (1 ≤ headL ∧ tailL = 0 ∧ headR = 0 ∧ 1 ≤ tailR) ∨
          (headL = 0 ∧ 1 ≤ tailL ∧ 1 ≤ headR ∧ tailR = 0) := by
        have := hL_pos
        have := hR_pos
        omega
      rcases hshape with hsplit | hsplit
      · exact Or.inr (Or.inl hsplit)
      · exact Or.inr (Or.inr hsplit)

/-- In the pure cross-boundary split case "left only in head, right only in
    tail", the head-side left contribution cannot be `≥ 2` under `¬EC`,
    because `wrap_head_toggleFR_left_ec` would already fire. So the head-side
    contribution is exactly the singleton `1`. -/
private theorem cyclic_wrap_split_left_head_singleton
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min : Fin gc.configs.length)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hnoEC : ¬hasEntryConflict gc)
    (hheadL_pos : 1 ≤ gc.intervalFireCount (left t) 0 s_min.val)
    (hheadR0 : gc.intervalFireCount (right t) 0 s_min.val = 0) :
    gc.intervalFireCount (left t) 0 s_min.val = 1 := by
  by_cases hheadL2 : 2 ≤ gc.intervalFireCount (left t) 0 s_min.val
  · exfalso
    exact hnoEC (wrap_head_toggleFR_left_ec gc t hbL hbR s_min hs_min_fire
      hno_t_before hheadL2 hheadR0)
  · omega

/-- Symmetric singleton reduction for the pure cross-boundary split
    "right only in head, left only in tail". -/
private theorem cyclic_wrap_split_right_head_singleton
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min : Fin gc.configs.length)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hnoEC : ¬hasEntryConflict gc)
    (hheadR_pos : 1 ≤ gc.intervalFireCount (right t) 0 s_min.val)
    (hheadL0 : gc.intervalFireCount (left t) 0 s_min.val = 0) :
    gc.intervalFireCount (right t) 0 s_min.val = 1 := by
  by_cases hheadR2 : 2 ≤ gc.intervalFireCount (right t) 0 s_min.val
  · exfalso
    exact hnoEC (wrap_head_toggleFR_right_ec gc t hbL hbR s_min hs_min_fire
      hno_t_before hheadR2 hheadL0)
  · omega

/-- Final compile-safe shape reduction for positive wrap `≥ 2` under `¬EC`.
    After discharging both-even, odd one-sided, and head-mixed wrap, the only
    surviving wrap residues are:
    1. genuinely tail-mixed, or
    2. pure cross-boundary split with a singleton head contribution. -/
private theorem cyclic_wrap_final_shape_reduction
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (hnoEC : ¬hasEntryConflict gc)
    (hwrap_ge2 :
      2 ≤
        (gc.intervalFireCount (left t) 0 s_min.val +
          gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length) +
        (gc.intervalFireCount (right t) 0 s_min.val +
          gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length)) :
    (1 ≤ gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length ∧
      1 ≤ gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length) ∨
    (gc.intervalFireCount (left t) 0 s_min.val = 1 ∧
      gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length = 0 ∧
      gc.intervalFireCount (right t) 0 s_min.val = 0 ∧
      1 ≤ gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length) ∨
    (gc.intervalFireCount (left t) 0 s_min.val = 0 ∧
      1 ≤ gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length ∧
      gc.intervalFireCount (right t) 0 s_min.val = 1 ∧
      gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length = 0) := by
  rcases cyclic_wrap_mixed_shape_reduction gc hn t hbL hbR s_min s_max hs_lt hs_min_fire
      hno_t_before hno_t_after hnoEC hwrap_ge2 with htail | hsplitL | hsplitR
  · exact Or.inl htail
  · have hheadL1 := cyclic_wrap_split_left_head_singleton gc t hbL hbR s_min hs_min_fire
      hno_t_before hnoEC hsplitL.1 hsplitL.2.2.1
    exact Or.inr (Or.inl ⟨hheadL1, hsplitL.2.1, hsplitL.2.2.1, hsplitL.2.2.2⟩)
  · have hheadR1 := cyclic_wrap_split_right_head_singleton gc t hbL hbR s_min hs_min_fire
      hno_t_before hnoEC hsplitR.2.2.1 hsplitR.1
    exact Or.inr (Or.inr ⟨hsplitR.1, hsplitR.2.1, hheadR1, hsplitR.2.2.2⟩)

/-- In the pure split case `left=head`, `right=tail`, the step immediately
    before `s_min` must be `left t`. This is the boundary-adjacent refinement
    of the singleton-head split case. -/
private theorem pure_split_left_prev_eq_left
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hnoEC : ¬hasEntryConflict gc)
    (s_min : Fin gc.configs.length)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hheadR0 : gc.intervalFireCount (right t) 0 s_min.val = 0)
    (hs_min_pos : 0 < s_min.val) :
    gc.moverAt ⟨s_min.val - 1, by
      have := s_min.isLt
      omega⟩ = left t := by
  let prev : Fin gc.configs.length := ⟨s_min.val - 1, by
    have := s_min.isLt
    omega⟩
  have hprev_local :
      gc.moverAt prev = left t ∨ gc.moverAt prev = t ∨ gc.moverAt prev = right t := by
    simpa [prev, hs_min_fire] using prev_mover_local_of_noEC gc hnoEC s_min hs_min_pos
  have hprev_ne_t : gc.moverAt prev ≠ t := by
    exact hno_t_before prev (by
      dsimp [prev]
      omega)
  have hprev_ne_right : gc.moverAt prev ≠ right t := by
    exact noFire_of_ifc_zero gc (right t) (Nat.le_of_lt s_min.isLt) hheadR0
      prev (Nat.zero_le _) (by
        dsimp [prev]
        omega)
  rcases hprev_local with hL | hT | hR
  · exact hL
  · exact False.elim (hprev_ne_t hT)
  · exact False.elim (hprev_ne_right hR)

/-- Symmetric boundary-adjacent refinement for the pure split case
    `right=head`, `left=tail`. -/
private theorem pure_split_right_prev_eq_right
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hnoEC : ¬hasEntryConflict gc)
    (s_min : Fin gc.configs.length)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hheadL0 : gc.intervalFireCount (left t) 0 s_min.val = 0)
    (hs_min_pos : 0 < s_min.val) :
    gc.moverAt ⟨s_min.val - 1, by
      have := s_min.isLt
      omega⟩ = right t := by
  let prev : Fin gc.configs.length := ⟨s_min.val - 1, by
    have := s_min.isLt
    omega⟩
  have hprev_local :
      gc.moverAt prev = left t ∨ gc.moverAt prev = t ∨ gc.moverAt prev = right t := by
    simpa [prev, hs_min_fire] using prev_mover_local_of_noEC gc hnoEC s_min hs_min_pos
  have hprev_ne_t : gc.moverAt prev ≠ t := by
    exact hno_t_before prev (by
      dsimp [prev]
      omega)
  have hprev_ne_left : gc.moverAt prev ≠ left t := by
    exact noFire_of_ifc_zero gc (left t) (Nat.le_of_lt s_min.isLt) hheadL0
      prev (Nat.zero_le _) (by
        dsimp [prev]
        omega)
  rcases hprev_local with hL | hT | hR
  · exact False.elim (hprev_ne_left hL)
  · exact False.elim (hprev_ne_t hT)
  · exact hR
/-- Final boundary-adjacent reduction for positive wrap `≥ 2` under `¬EC`.
    After all currently formalized wrap mechanisms are applied, the remaining
    wrap residue is either genuinely tail-mixed, or a pure cross-boundary split
    whose boundary step `s_min - 1` is explicitly the singleton head neighbor. -/
private theorem cyclic_wrap_boundary_shape_reduction
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (hnoEC : ¬hasEntryConflict gc)
    (hwrap_ge2 :
      2 ≤
        (gc.intervalFireCount (left t) 0 s_min.val +
          gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length) +
        (gc.intervalFireCount (right t) 0 s_min.val +
          gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length)) :
    (1 ≤ gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length ∧
      1 ≤ gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length) ∨
    (gc.intervalFireCount (left t) 0 s_min.val = 1 ∧
      gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length = 0 ∧
      gc.intervalFireCount (right t) 0 s_min.val = 0 ∧
      1 ≤ gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length ∧
      gc.moverAt ⟨s_min.val - 1, by
        have := s_min.isLt
        omega⟩ = left t) ∨
    (gc.intervalFireCount (left t) 0 s_min.val = 0 ∧
      1 ≤ gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length ∧
      gc.intervalFireCount (right t) 0 s_min.val = 1 ∧
      gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length = 0 ∧
      gc.moverAt ⟨s_min.val - 1, by
        have := s_min.isLt
        omega⟩ = right t) := by
  rcases cyclic_wrap_final_shape_reduction gc hn t hbL hbR s_min s_max hs_lt hs_min_fire
      hno_t_before hno_t_after hnoEC hwrap_ge2 with htail | hsplitL | hsplitR
  · exact Or.inl htail
  · rcases hsplitL with ⟨hheadL1, htailL0, hheadR0, htailRpos⟩
    have hs_min_pos : 0 < s_min.val := by
      by_contra h
      have hs0 : s_min.val = 0 := by omega
      rw [hs0] at hheadL1
      simp [GoodCycle.intervalFireCount] at hheadL1
    have hprev_left := pure_split_left_prev_eq_left gc t hnoEC s_min hs_min_fire
      hno_t_before hheadR0 hs_min_pos
    exact Or.inr (Or.inl ⟨hheadL1, htailL0, hheadR0, htailRpos, hprev_left⟩)
  · rcases hsplitR with ⟨hheadL0, htailLpos, hheadR1, htailR0⟩
    have hs_min_pos : 0 < s_min.val := by
      by_contra h
      have hs0 : s_min.val = 0 := by omega
      rw [hs0] at hheadR1
      simp [GoodCycle.intervalFireCount] at hheadR1
    have hprev_right := pure_split_right_prev_eq_right gc t hnoEC s_min hs_min_fire
      hno_t_before hheadL0 hs_min_pos
    exact Or.inr (Or.inr ⟨hheadL0, htailLpos, hheadR1, htailR0, hprev_right⟩)

/-- In the pure split case `left=head`, `right=tail`, the first tail step after
    `s_max` is forced to be `right t`. -/
private theorem pure_split_left_next_eq_right
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (s_max : Fin gc.configs.length)
    (hs_max_fire : gc.moverAt s_max = t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (htailL0 : gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length = 0)
    (htailR_pos : 1 ≤ gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length) :
    gc.moverAt (nextIndex gc.configs s_max) = right t := by
  have hs1_lt : s_max.val + 1 < gc.configs.length := by
    by_contra h
    have hlast : s_max.val + 1 = gc.configs.length := by omega
    rw [hlast] at htailR_pos
    simp [GoodCycle.intervalFireCount] at htailR_pos
  let nxt : Fin gc.configs.length := ⟨s_max.val + 1, hs1_lt⟩
  have hnxt_eq : nextIndex gc.configs s_max = nxt := by
    apply Fin.ext
    simp [nextIndex, nxt, Nat.mod_eq_of_lt hs1_lt]
  have hlocal := gc.next_mover_is_local s_max
  rw [hs_max_fire, hnxt_eq] at hlocal
  have hnxt_ne_t : gc.moverAt nxt ≠ t := by
    exact hno_t_after nxt (by
      dsimp [nxt]
      omega)
  have hnxt_ne_left : gc.moverAt nxt ≠ left t := by
    exact noFire_of_ifc_zero gc (left t) le_rfl htailL0
      nxt (by
        dsimp [nxt]
        omega) nxt.isLt
  rcases hlocal with hL | hT | hR
  · exact False.elim (hnxt_ne_left hL)
  · exact False.elim (hnxt_ne_t hT)
  · simpa [hnxt_eq] using hR

/-- Symmetric first-tail-step identification in the pure split case
    `right=head`, `left=tail`. -/
private theorem pure_split_right_next_eq_left
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (s_max : Fin gc.configs.length)
    (hs_max_fire : gc.moverAt s_max = t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (htailR0 : gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length = 0)
    (htailL_pos : 1 ≤ gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length) :
    gc.moverAt (nextIndex gc.configs s_max) = left t := by
  have hs1_lt : s_max.val + 1 < gc.configs.length := by
    by_contra h
    have hlast : s_max.val + 1 = gc.configs.length := by omega
    rw [hlast] at htailL_pos
    simp [GoodCycle.intervalFireCount] at htailL_pos
  let nxt : Fin gc.configs.length := ⟨s_max.val + 1, hs1_lt⟩
  have hnxt_eq : nextIndex gc.configs s_max = nxt := by
    apply Fin.ext
    simp [nextIndex, nxt, Nat.mod_eq_of_lt hs1_lt]
  have hlocal := gc.next_mover_is_local s_max
  rw [hs_max_fire, hnxt_eq] at hlocal
  have hnxt_ne_t : gc.moverAt nxt ≠ t := by
    exact hno_t_after nxt (by
      dsimp [nxt]
      omega)
  have hnxt_ne_right : gc.moverAt nxt ≠ right t := by
    exact noFire_of_ifc_zero gc (right t) le_rfl htailR0
      nxt (by
        dsimp [nxt]
        omega) nxt.isLt
  rcases hlocal with hL | hT | hR
  · simpa [hnxt_eq] using hL
  · exact False.elim (hnxt_ne_t hT)
  · exact False.elim (hnxt_ne_right hR)

/-- In the pure split case `left=head`, `right=tail`, the boundary around the
    wrap cut is now completely explicit:
    `s_min - 1` is `left t` and the first tail step after `s_max` is `right t`.
    This packages the current live reduction of that residue to a concrete local
    block. -/
private theorem pure_split_left_boundary_block
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hnoEC : ¬hasEntryConflict gc)
    (s_min s_max : Fin gc.configs.length)
    (hs_min_fire : gc.moverAt s_min = t)
    (hs_max_fire : gc.moverAt s_max = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (hheadL1 : gc.intervalFireCount (left t) 0 s_min.val = 1)
    (hheadR0 : gc.intervalFireCount (right t) 0 s_min.val = 0)
    (htailL0 : gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length = 0)
    (htailR_pos : 1 ≤ gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length) :
    gc.moverAt ⟨s_min.val - 1, by
      have := s_min.isLt
      omega⟩ = left t ∧
    gc.moverAt (nextIndex gc.configs s_max) = right t := by
  have hs_min_pos : 0 < s_min.val := by
    by_contra h
    have hs0 : s_min.val = 0 := by omega
    rw [hs0] at hheadL1
    simp [GoodCycle.intervalFireCount] at hheadL1
  exact ⟨pure_split_left_prev_eq_left gc t hnoEC s_min hs_min_fire hno_t_before hheadR0 hs_min_pos,
    pure_split_left_next_eq_right gc t s_max hs_max_fire hno_t_after htailL0 htailR_pos⟩

/-- Symmetric boundary-block package for the pure split case
    `right=head`, `left=tail`. -/
private theorem pure_split_right_boundary_block
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hnoEC : ¬hasEntryConflict gc)
    (s_min s_max : Fin gc.configs.length)
    (hs_min_fire : gc.moverAt s_min = t)
    (hs_max_fire : gc.moverAt s_max = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (hheadL0 : gc.intervalFireCount (left t) 0 s_min.val = 0)
    (hheadR1 : gc.intervalFireCount (right t) 0 s_min.val = 1)
    (htailL_pos : 1 ≤ gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length)
    (htailR0 : gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length = 0) :
    gc.moverAt ⟨s_min.val - 1, by
      have := s_min.isLt
      omega⟩ = right t ∧
    gc.moverAt (nextIndex gc.configs s_max) = left t := by
  have hs_min_pos : 0 < s_min.val := by
    by_contra h
    have hs0 : s_min.val = 0 := by omega
    rw [hs0] at hheadR1
    simp [GoodCycle.intervalFireCount] at hheadR1
  exact ⟨pure_split_right_prev_eq_right gc t hnoEC s_min hs_min_fire hno_t_before hheadL0 hs_min_pos,
    pure_split_right_next_eq_left gc t s_max hs_max_fire hno_t_after htailR0 htailL_pos⟩

/-- Final concrete reduction for positive wrap `≥ 2` under `¬EC`.
    The only surviving wrap residues are:
    1. genuinely tail-mixed, or
    2. a pure cross-boundary block already pinned as
       `t, right t, ..., left t, t` or the mirror. -/
private theorem cyclic_wrap_explicit_boundary_block_reduction
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hs_min_fire : gc.moverAt s_min = t)
    (hs_max_fire : gc.moverAt s_max = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (hnoEC : ¬hasEntryConflict gc)
    (hwrap_ge2 :
      2 ≤
        (gc.intervalFireCount (left t) 0 s_min.val +
          gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length) +
        (gc.intervalFireCount (right t) 0 s_min.val +
          gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length)) :
    (1 ≤ gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length ∧
      1 ≤ gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length) ∨
    (gc.intervalFireCount (left t) 0 s_min.val = 1 ∧
      gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length = 0 ∧
      gc.intervalFireCount (right t) 0 s_min.val = 0 ∧
      1 ≤ gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length ∧
      gc.moverAt ⟨s_min.val - 1, by
        have := s_min.isLt
        omega⟩ = left t ∧
      gc.moverAt (nextIndex gc.configs s_max) = right t) ∨
    (gc.intervalFireCount (left t) 0 s_min.val = 0 ∧
      1 ≤ gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length ∧
      gc.intervalFireCount (right t) 0 s_min.val = 1 ∧
      gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length = 0 ∧
      gc.moverAt ⟨s_min.val - 1, by
        have := s_min.isLt
        omega⟩ = right t ∧
      gc.moverAt (nextIndex gc.configs s_max) = left t) := by
  rcases cyclic_wrap_boundary_shape_reduction gc hn t hbL hbR s_min s_max hs_lt hs_min_fire
      hno_t_before hno_t_after hnoEC hwrap_ge2 with htail | hsplitL | hsplitR
  · exact Or.inl htail
  · rcases hsplitL with ⟨hheadL1, htailL0, hheadR0, htailRpos, hprev_left⟩
    have hblock := pure_split_left_boundary_block gc t hnoEC s_min s_max hs_min_fire hs_max_fire
      hno_t_before hno_t_after hheadL1 hheadR0 htailL0 htailRpos
    exact Or.inr (Or.inl ⟨hheadL1, htailL0, hheadR0, htailRpos, hblock.1, hblock.2⟩)
  · rcases hsplitR with ⟨hheadL0, htailLpos, hheadR1, htailR0, hprev_right⟩
    have hblock := pure_split_right_boundary_block gc t hnoEC s_min s_max hs_min_fire hs_max_fire
      hno_t_before hno_t_after hheadL0 hheadR1 htailLpos htailR0
    exact Or.inr (Or.inr ⟨hheadL0, htailLpos, hheadR1, htailR0, hblock.1, hblock.2⟩)

/-- Auto-chosen `s_min` / `s_max` wrapper for
    `cyclic_wrap_explicit_boundary_block_reduction`. This packages the final
    compile-safe wrap-shape reduction at the same abstraction level as the
    other live auto wrappers in `NormalFormEC`. -/
private theorem cyclic_wrap_explicit_boundary_block_reduction_auto
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (hfc_t_ge2 : gc.fireCount t ≥ 2)
    (hnoEC : ¬hasEntryConflict gc)
    (hwrap_ge2 :
      let tFires : Finset (Fin gc.configs.length) :=
        Finset.univ.filter (fun k => gc.moverAt k = t)
      let s_min : Fin gc.configs.length := tFires.min' (by
        have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc_t_ge2
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
      let s_max : Fin gc.configs.length := tFires.max' (by
        have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc_t_ge2
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
      2 ≤
        (gc.intervalFireCount (left t) 0 s_min.val +
          gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length) +
        (gc.intervalFireCount (right t) 0 s_min.val +
          gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length)) :
    (let tFires : Finset (Fin gc.configs.length) :=
        Finset.univ.filter (fun k => gc.moverAt k = t)
      let s_min : Fin gc.configs.length := tFires.min' (by
        have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc_t_ge2
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
      let s_max : Fin gc.configs.length := tFires.max' (by
        have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc_t_ge2
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
      (1 ≤ gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length ∧
        1 ≤ gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length) ∨
      (gc.intervalFireCount (left t) 0 s_min.val = 1 ∧
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length = 0 ∧
        gc.intervalFireCount (right t) 0 s_min.val = 0 ∧
        1 ≤ gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length ∧
        gc.moverAt ⟨s_min.val - 1, by
          have := s_min.isLt
          omega⟩ = left t ∧
        gc.moverAt (nextIndex gc.configs s_max) = right t) ∨
      (gc.intervalFireCount (left t) 0 s_min.val = 0 ∧
        1 ≤ gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length ∧
        gc.intervalFireCount (right t) 0 s_min.val = 1 ∧
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length = 0 ∧
        gc.moverAt ⟨s_min.val - 1, by
          have := s_min.isLt
          omega⟩ = right t ∧
        gc.moverAt (nextIndex gc.configs s_max) = left t)) := by
  classical
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
      rw [← heq] at hle2
      exact le_antisymm hle2 hle1
    have hfc_le1 : gc.fireCount t ≤ 1 := by
      rw [gc.fireCount_eq_sum_moverAt t]
      have hbd : ∀ j : Fin gc.configs.length,
          (if gc.moverAt j = t then (1 : Nat) else 0) ≤
            (if j = s_min then 1 else 0) := by
        intro j
        by_cases hj : gc.moverAt j = t
        · rw [huniq j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)]
          simp [hs_min_fire]
        · simp [hj]
      calc ∑ j, (if gc.moverAt j = t then (1 : Nat) else 0)
          ≤ ∑ j, (if j = s_min then 1 else 0) :=
            Finset.sum_le_sum (fun j _ => hbd j)
        _ = 1 := by
          rw [Finset.sum_eq_single s_min
            (fun b _ hb => by simp [hb]) (by simp)]
          simp
    omega
  have hs_lt : s_min.val < s_max.val := by
    have hle : s_min ≤ s_max := Finset.min'_le tFires s_max (Finset.max'_mem tFires htFires_ne)
    exact lt_of_le_of_ne hle (fun h => hs_ne (Fin.ext h))
  have hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t := by
    intro k hk
    intro hfire
    have hk_mem : k ∈ tFires := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hfire⟩
    have := Finset.min'_le tFires k hk_mem
    omega
  have hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t := by
    intro k hk
    intro hfire
    have hk_mem : k ∈ tFires := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hfire⟩
    have := Finset.le_max' tFires k hk_mem
    omega
  exact cyclic_wrap_explicit_boundary_block_reduction gc hn t hbL hbR s_min s_max hs_lt
    hs_min_fire hs_max_fire hno_t_before hno_t_after hnoEC (by
      dsimp [tFires, s_min, s_max] at hwrap_ge2 ⊢
      exact hwrap_ge2)

/-- If every non-empty `TernaryPhase` whose first step is adjacent to `t`
    has first-neighbor sum at most `1`, then every linear consecutive `t`-pair
    also has combined first-neighbor count at most `1`. Empty gaps contribute
    `0`; non-empty gaps are converted to a `TernaryPhase` starting at `a+1`. -/
private theorem consecutive_tpair_sum_le1_of_phase_bound
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (h_phase_le1 : ∀ phase : TernaryPhase gc t,
      (gc.moverAt phase.a = left t ∨ gc.moverAt phase.a = right t) →
      gc.intervalFireCount (left t) phase.a.val phase.s.val +
        gc.intervalFireCount (right t) phase.a.val phase.s.val ≤ 1) :
    ∀ (a s : Fin gc.configs.length),
      a.val < s.val →
      gc.moverAt a = t → gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      gc.intervalFireCount (left t) a.val s.val +
        gc.intervalFireCount (right t) a.val s.val ≤ 1 := by
  intro a s has ha hs hno
  have hstepL : gc.intervalFireCount (left t) a.val (a.val + 1) = 0 := by
    rw [intervalFireCount_single gc (left t) a.isLt]
    simp [show gc.moverAt a ≠ left t from by
      rw [ha]
      exact (left_ne_self_nfec t).symm]
  have hstepR : gc.intervalFireCount (right t) a.val (a.val + 1) = 0 := by
    rw [intervalFireCount_single gc (right t) a.isLt]
    simp [show gc.moverAt a ≠ right t from by
      rw [ha]
      exact (right_ne_self_nfec t).symm]
  by_cases hgap : a.val + 1 < s.val
  · have ha1_lt : a.val + 1 < gc.configs.length := by omega
    let a1 : Fin gc.configs.length := ⟨a.val + 1, ha1_lt⟩
    have ha1_nonmover : gc.moverAt a1 ≠ t :=
      hno a1 (by
        dsimp [a1]
        omega) hgap
    have ha1_nofire : ∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ t :=
      fun k hk1 hk2 => hno k (by
        dsimp [a1] at hk1
        omega) hk2
    let phase : TernaryPhase gc t :=
      { a := a1, s := s, ha_lt_s := hgap, hs_mover := hs,
        ha_nonmover := ha1_nonmover, ht_nofire := ha1_nofire }
    have ha_adj : gc.moverAt a1 = left t ∨ gc.moverAt a1 = right t := by
      have hnext_local := gc.next_mover_is_local a
      have hnext_eq : nextIndex gc.configs a = a1 := by
        apply Fin.ext
        simp [nextIndex, a1]
        exact Nat.mod_eq_of_lt ha1_lt
      rw [ha, hnext_eq] at hnext_local
      rcases hnext_local with hleft | hself | hright
      · exact Or.inl hleft
      · exfalso
        exact ha1_nonmover hself
      · exact Or.inr hright
    have hle := h_phase_le1 phase ha_adj
    have hle' :
        gc.intervalFireCount (left t) a1.val s.val +
          gc.intervalFireCount (right t) a1.val s.val ≤ 1 := by
      simpa [phase] using hle
    have hsplitL := intervalFireCount_split gc (left t)
      (show a.val ≤ a.val + 1 by omega)
      (show a.val + 1 ≤ s.val by omega)
    have hsplitR := intervalFireCount_split gc (right t)
      (show a.val ≤ a.val + 1 by omega)
      (show a.val + 1 ≤ s.val by omega)
    have ha1_val : a1.val = a.val + 1 := rfl
    have hsum_shift :
        gc.intervalFireCount (left t) a.val s.val +
          gc.intervalFireCount (right t) a.val s.val =
        gc.intervalFireCount (left t) a1.val s.val +
          gc.intervalFireCount (right t) a1.val s.val := by
      rw [ha1_val]
      omega
    rw [hsum_shift]
    exact hle'
  · have heq : a.val + 1 = s.val := by omega
    have hsplitL := intervalFireCount_split gc (left t)
      (show a.val ≤ a.val + 1 by omega)
      (show a.val + 1 ≤ s.val by omega)
    have hsplitR := intervalFireCount_split gc (right t)
      (show a.val ≤ a.val + 1 by omega)
      (show a.val + 1 ≤ s.val by omega)
    have htailL : gc.intervalFireCount (left t) (a.val + 1) s.val = 0 := by
      rw [heq]
      simp [GoodCycle.intervalFireCount]
    have htailR : gc.intervalFireCount (right t) (a.val + 1) s.val = 0 := by
      rw [heq]
      simp [GoodCycle.intervalFireCount]
    omega

/-- The combined `left t` / `right t` fire count on the linear interval from the
    first to the last `t`-fire is at most `fireCount t - 1`, provided every
    linear consecutive `t`-pair has first-neighbor sum at most `1`. -/
private theorem interior_neighbor_sum_le_of_consec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hfc_t_ge2 : gc.fireCount t ≥ 2)
    (h_consec_le1 : ∀ (a s : Fin gc.configs.length),
      a.val < s.val →
      gc.moverAt a = t → gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      gc.intervalFireCount (left t) a.val s.val +
        gc.intervalFireCount (right t) a.val s.val ≤ 1) :
    let tFires : Finset (Fin gc.configs.length) :=
      Finset.univ.filter (fun k => gc.moverAt k = t)
    let s_min : Fin gc.configs.length := tFires.min' (by
      have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc_t_ge2
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
    let s_max : Fin gc.configs.length := tFires.max' (by
      have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc_t_ge2
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
    gc.intervalFireCount (left t) s_min.val s_max.val +
      gc.intervalFireCount (right t) s_min.val s_max.val ≤ gc.fireCount t - 1 := by
  classical
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
      rw [← heq] at hle2
      exact le_antisymm hle2 hle1
    have hfc_le1 : gc.fireCount t ≤ 1 := by
      rw [gc.fireCount_eq_sum_moverAt t]
      have hbd : ∀ j : Fin gc.configs.length,
          (if gc.moverAt j = t then (1 : Nat) else 0) ≤
            (if j = s_min then 1 else 0) := by
        intro j
        by_cases hj : gc.moverAt j = t
        · rw [huniq j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)]
          simp [hs_min_fire]
        · simp [hj]
      calc ∑ j, (if gc.moverAt j = t then (1 : Nat) else 0)
          ≤ ∑ j, (if j = s_min then 1 else 0) :=
            Finset.sum_le_sum (fun j _ => hbd j)
        _ = 1 := by
          rw [Finset.sum_eq_single s_min
            (fun b _ hb => by simp [hb]) (by simp)]
          simp
    omega
  have hs_lt : s_min.val < s_max.val := by
    have hle : s_min ≤ s_max := Finset.min'_le tFires s_max (Finset.max'_mem tFires htFires_ne)
    exact lt_of_le_of_ne hle (fun h => hs_ne (Fin.ext h))
  have hinterior := ifc_sum_le_of_consec_le1 gc t (left t) (right t) h_consec_le1
    (s_max.val - s_min.val) s_min s_max le_rfl hs_lt hs_min_fire hs_max_fire
  have hifc_t_mid : gc.intervalFireCount t s_min.val s_max.val = gc.fireCount t - 1 := by
    have hfull := fireCount_eq_intervalFireCount_full gc t
    have split_mid := intervalFireCount_split gc t (show s_min.val ≤ s_max.val by omega)
      (show s_max.val ≤ gc.configs.length by exact Nat.le_of_lt s_max.isLt)
    have split_all := intervalFireCount_split gc t (Nat.zero_le s_min.val)
      (show s_min.val ≤ gc.configs.length by exact Nat.le_of_lt s_min.isLt)
    rw [← hfull, split_mid] at split_all
    have hifc_t_before : gc.intervalFireCount t 0 s_min.val = 0 := by
      apply intervalFireCount_eq_zero_of_noFire gc t (Nat.zero_le _) (Nat.le_of_lt s_min.isLt)
      intro k hk1 hk2
      intro hfire
      have hk_mem : k ∈ tFires := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hfire⟩
      have := Finset.min'_le tFires k hk_mem
      omega
    have hifc_t_after : gc.intervalFireCount t s_max.val gc.configs.length = 1 := by
      have h_smax_one : gc.intervalFireCount t s_max.val (s_max.val + 1) = 1 := by
        rw [intervalFireCount_single gc t s_max.isLt]
        simp [hs_max_fire]
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
    omega
  rw [hifc_t_mid] at hinterior
  exact hinterior

/-- For any processor `p ≠ t`, its total fire count decomposes into the linear
    interior contribution between the first and last `t`-fires plus the cyclic
    wrap contribution before the first and after the last. -/
private theorem fireCount_eq_interior_plus_wrap_of_ne_t
    (gc : GoodCycle sys) (t p : Fin sys.rs.n)
    (hfc_t_ge2 : gc.fireCount t ≥ 2)
    (hp_ne_t : p ≠ t) :
    let tFires : Finset (Fin gc.configs.length) :=
      Finset.univ.filter (fun k => gc.moverAt k = t)
    let s_min : Fin gc.configs.length := tFires.min' (by
      have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc_t_ge2
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
    let s_max : Fin gc.configs.length := tFires.max' (by
      have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc_t_ge2
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
    gc.fireCount p =
      gc.intervalFireCount p s_min.val s_max.val +
        (gc.intervalFireCount p 0 s_min.val +
          gc.intervalFireCount p (s_max.val + 1) gc.configs.length) := by
  classical
  let tFires : Finset (Fin gc.configs.length) :=
    Finset.univ.filter (fun k => gc.moverAt k = t)
  have htFires_ne : tFires.Nonempty := by
    have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc_t_ge2
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  let s_min : Fin gc.configs.length := tFires.min' htFires_ne
  let s_max : Fin gc.configs.length := tFires.max' htFires_ne
  have hs_max_fire : gc.moverAt s_max = t :=
    (Finset.mem_filter.mp (Finset.max'_mem tFires htFires_ne)).2
  have hs_ne : s_min ≠ s_max := by
    intro heq
    have huniq : ∀ k ∈ tFires, k = s_min := by
      intro k hk
      have hle1 : s_min ≤ k := Finset.min'_le tFires k hk
      have hle2 : k ≤ s_max := Finset.le_max' tFires k hk
      rw [← heq] at hle2
      exact le_antisymm hle2 hle1
    have hfc_le1 : gc.fireCount t ≤ 1 := by
      rw [gc.fireCount_eq_sum_moverAt t]
      have hbd : ∀ j : Fin gc.configs.length,
          (if gc.moverAt j = t then (1 : Nat) else 0) ≤
            (if j = s_min then 1 else 0) := by
        intro j
        by_cases hj : gc.moverAt j = t
        · rw [huniq j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)]
          simp [show gc.moverAt s_min = t from
            (Finset.mem_filter.mp (Finset.min'_mem tFires htFires_ne)).2]
        · simp [hj]
      calc ∑ j, (if gc.moverAt j = t then (1 : Nat) else 0)
          ≤ ∑ j, (if j = s_min then 1 else 0) :=
            Finset.sum_le_sum (fun j _ => hbd j)
        _ = 1 := by
          rw [Finset.sum_eq_single s_min
            (fun b _ hb => by simp [hb]) (by simp)]
          simp
    omega
  have hs_lt : s_min.val < s_max.val := by
    have hle : s_min ≤ s_max := Finset.min'_le tFires s_max (Finset.max'_mem tFires htFires_ne)
    exact lt_of_le_of_ne hle (fun h => hs_ne (Fin.ext h))
  have hstep_smax : gc.intervalFireCount p s_max.val (s_max.val + 1) = 0 := by
    rw [intervalFireCount_single gc p s_max.isLt]
    simp [show gc.moverAt s_max ≠ p from by
      rw [hs_max_fire]
      exact hp_ne_t.symm]
  have hsplit := intervalFireCount_split gc p
    (show s_min.val ≤ s_max.val by omega)
    (show s_max.val ≤ s_max.val + 1 by omega)
  have hmid_eq : gc.intervalFireCount p s_min.val (s_max.val + 1) =
      gc.intervalFireCount p s_min.val s_max.val := by
    omega
  have hmid_le : gc.intervalFireCount p s_min.val (s_max.val + 1) ≤ gc.fireCount p := by
    have hfull := fireCount_eq_intervalFireCount_full gc p
    have h1 := intervalFireCount_split gc p (Nat.zero_le s_min.val)
      (show s_min.val ≤ gc.configs.length by exact Nat.le_of_lt s_min.isLt)
    have h2 := intervalFireCount_split gc p
      (show s_min.val ≤ s_max.val + 1 by omega)
      (show s_max.val + 1 ≤ gc.configs.length by omega)
    omega
  have hwrap := wrap_ifc_eq gc p s_min.isLt s_max.isLt (Nat.le_of_lt hs_lt)
  have hfc_eq : gc.fireCount p =
      gc.intervalFireCount p s_min.val (s_max.val + 1) +
        (gc.intervalFireCount p 0 s_min.val +
          gc.intervalFireCount p (s_max.val + 1) gc.configs.length) := by
    omega
  rw [hmid_eq] at hfc_eq
  exact hfc_eq

/-- Explicit interval decomposition for `p ≠ t`: if `s_max` is a `t`-fire, then
    the single-step interval `[s_max, s_max+1)` contributes `0` to `p`, so the
    total fire count of `p` splits into the linear interior `[s_min, s_max)` plus
    the wrap contribution before `s_min` and after `s_max`. -/
private theorem fireCount_eq_interior_plus_wrap_of_ne_t_explicit
    (gc : GoodCycle sys) (t p : Fin sys.rs.n)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hs_max_fire : gc.moverAt s_max = t)
    (hp_ne_t : p ≠ t) :
    gc.fireCount p =
      gc.intervalFireCount p s_min.val s_max.val +
        (gc.intervalFireCount p 0 s_min.val +
          gc.intervalFireCount p (s_max.val + 1) gc.configs.length) := by
  have hstep_smax : gc.intervalFireCount p s_max.val (s_max.val + 1) = 0 := by
    rw [intervalFireCount_single gc p s_max.isLt]
    simp [show gc.moverAt s_max ≠ p from by
      rw [hs_max_fire]
      exact hp_ne_t.symm]
  have hsplit_mid := intervalFireCount_split gc p
    (show s_min.val ≤ s_max.val by omega)
    (show s_max.val ≤ s_max.val + 1 by omega)
  have hmid_eq : gc.intervalFireCount p s_min.val (s_max.val + 1) =
      gc.intervalFireCount p s_min.val s_max.val := by
    omega
  have hfull := fireCount_eq_intervalFireCount_full gc p
  have hsplit0 := intervalFireCount_split gc p (Nat.zero_le s_min.val)
    (show s_min.val ≤ gc.configs.length by exact Nat.le_of_lt s_min.isLt)
  have hsplit1 := intervalFireCount_split gc p
    (show s_min.val ≤ s_max.val + 1 by omega)
    (show s_max.val + 1 ≤ gc.configs.length by omega)
  rw [← hfull, hsplit1] at hsplit0
  rw [hmid_eq] at hsplit0
  omega

/-- If `s_min` and `s_max` are the first and last linear `t`-fires, then the
    interior `t`-fire count between them is exactly `fireCount t - 1`. -/
private theorem t_fireCount_between_first_last
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hfc_t_ge2 : gc.fireCount t ≥ 2)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hs_min_fire : gc.moverAt s_min = t)
    (hs_max_fire : gc.moverAt s_max = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t) :
    gc.intervalFireCount t s_min.val s_max.val = gc.fireCount t - 1 := by
  have hfull := fireCount_eq_intervalFireCount_full gc t
  have hifc_t_before : gc.intervalFireCount t 0 s_min.val = 0 := by
    apply intervalFireCount_eq_zero_of_noFire gc t (Nat.zero_le _) (Nat.le_of_lt s_min.isLt)
    intro k _ hk2
    exact hno_t_before k hk2
  have hifc_t_after : gc.intervalFireCount t s_max.val gc.configs.length = 1 := by
    have h_smax_one : gc.intervalFireCount t s_max.val (s_max.val + 1) = 1 := by
      rw [intervalFireCount_single gc t s_max.isLt]
      simp [hs_max_fire]
    have h_after_zero : gc.intervalFireCount t (s_max.val + 1) gc.configs.length = 0 := by
      apply intervalFireCount_eq_zero_of_noFire gc t (by omega) le_rfl
      intro k hk1 hk2
      exact hno_t_after k (by omega)
    have := intervalFireCount_split gc t (show s_max.val ≤ s_max.val + 1 by omega)
      (show s_max.val + 1 ≤ gc.configs.length by omega)
    omega
  have split_mid := intervalFireCount_split gc t (show s_min.val ≤ s_max.val by omega)
    (show s_max.val ≤ gc.configs.length by exact Nat.le_of_lt s_max.isLt)
  have split_all := intervalFireCount_split gc t (Nat.zero_le s_min.val)
    (show s_min.val ≤ gc.configs.length by exact Nat.le_of_lt s_min.isLt)
  rw [← hfull, split_mid] at split_all
  omega

/-- If the combined first-neighbor fire count is at most `fireCount t`, then
    the right neighbor fires at least `2` fewer times than `t`, so there is a
    consecutive linear `t`-pair with zero `right t` fires in between. -/
private theorem exists_zero_right_gap_of_neighbor_sum_le
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0)
    (hfc_t_ge2 : gc.fireCount t ≥ 2)
    (hfc_t_lt_L : gc.fireCount t < gc.configs.length)
    (hsum_le : gc.fireCount (left t) + gc.fireCount (right t) ≤ gc.fireCount t) :
    ∃ (a s : Fin gc.configs.length),
      a.val < s.val ∧
      gc.moverAt a = t ∧
      gc.moverAt s = t ∧
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) ∧
      gc.intervalFireCount (right t) a.val s.val = 0 := by
  have hfc_left_pos : gc.fireCount (left t) > 0 := hfull (left t)
  have hfc_left_ge2 : gc.fireCount (left t) ≥ 2 := by
    obtain ⟨m, hm⟩ := gc.binary_fireCount_even (left t) hbL
    omega
  have hfc_right_lt_t : gc.fireCount (right t) + 2 ≤ gc.fireCount t := by
    omega
  exact exists_consecutive_tfire_with_zero_qfire gc t (right t)
    hfc_t_ge2 hfc_t_lt_L hfc_right_lt_t

/-- A non-empty consecutive `t`-pair with zero `right t` fires is forced to be
    a left-sided phase whose first step is `left t`, and whose suffix from
    `a+1` to `s` has `(J,K) = (1,0)`. -/
private theorem zero_right_gap_nonempty_gives_left_phase_data
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (a s : Fin gc.configs.length)
    (has : a.val < s.val)
    (ha : gc.moverAt a = t) (hs : gc.moverAt s = t)
    (hno_t : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t)
    (hpair_le1 :
      gc.intervalFireCount (left t) a.val s.val +
        gc.intervalFireCount (right t) a.val s.val ≤ 1)
    (hifcR0 : gc.intervalFireCount (right t) a.val s.val = 0)
    (hgap : a.val + 1 < s.val) :
    let a1 : Fin gc.configs.length := ⟨a.val + 1, by
      have := s.isLt
      omega⟩
    gc.moverAt a1 = left t ∧
      gc.intervalFireCount (left t) a1.val s.val = 1 ∧
      gc.intervalFireCount (right t) a1.val s.val = 0 := by
  have ha1_lt_len : a.val + 1 < gc.configs.length := by
    have := s.isLt
    omega
  let a1 : Fin gc.configs.length := ⟨a.val + 1, ha1_lt_len⟩
  have ha1_val : a1.val = a.val + 1 := rfl
  have ha1_nonmover : gc.moverAt a1 ≠ t := hno_t a1 (by
    dsimp [a1]
    omega) hgap
  have ha1_adj : gc.moverAt a1 = left t ∨ gc.moverAt a1 = right t := by
    have hnext_local := gc.next_mover_is_local a
    have hnext_eq : nextIndex gc.configs a = a1 := by
      apply Fin.ext
      simp [nextIndex, a1]
      exact Nat.mod_eq_of_lt ha1_lt_len
    rw [ha, hnext_eq] at hnext_local
    rcases hnext_local with hleft | hself | hright
    · exact Or.inl hleft
    · exfalso
      exact ha1_nonmover hself
    · exact Or.inr hright
  have ha1_not_right : gc.moverAt a1 ≠ right t := by
    exact noFire_of_ifc_zero gc (right t) (Nat.le_of_lt s.isLt) hifcR0
      a1 (by
        dsimp [a1]
        omega) hgap
  have ha1_left : gc.moverAt a1 = left t := by
    rcases ha1_adj with hleft | hright
    · exact hleft
    · exfalso
      exact ha1_not_right hright
  have hstepL0 : gc.intervalFireCount (left t) a.val a1.val = 0 := by
    rw [ha1_val, intervalFireCount_single gc (left t) a.isLt]
    simp [ha, show t ≠ left t from (left_ne_self_nfec t).symm]
  have hstepR0 : gc.intervalFireCount (right t) a.val a1.val = 0 := by
    rw [ha1_val, intervalFireCount_single gc (right t) a.isLt]
    simp [ha, show t ≠ right t from (right_ne_self_nfec t).symm]
  have ha1succ_lt : a1.val + 1 ≤ s.val := by
    dsimp [a1] at hgap ⊢
    omega
  have hstepA1L : gc.intervalFireCount (left t) a1.val (a1.val + 1) = 1 := by
    rw [intervalFireCount_single gc (left t) a1.isLt]
    simp [ha1_left]
  have hsplitL := intervalFireCount_split gc (left t)
    (show a.val ≤ a1.val by omega) (show a1.val ≤ s.val by omega)
  have hsplitR := intervalFireCount_split gc (right t)
    (show a.val ≤ a1.val by omega) (show a1.val ≤ s.val by omega)
  have hsplitA1L := intervalFireCount_split gc (left t)
    (show a1.val ≤ a1.val + 1 by omega) ha1succ_lt
  have hleft_le1 : gc.intervalFireCount (left t) a1.val s.val ≤ 1 := by
    omega
  have hright0 : gc.intervalFireCount (right t) a1.val s.val = 0 := by
    omega
  have hleft_ge1 : 1 ≤ gc.intervalFireCount (left t) a1.val s.val := by
    omega
  refine ⟨ha1_left, ?_, ?_⟩
  · exact Nat.le_antisymm hleft_le1 hleft_ge1
  · exact hright0

/-- If the extracted left-phase data has at least one additional step after the
    initial `left t` fire, then the existing one-sided long-phase EC closes it
    immediately. -/
private theorem left_phase_data_long_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (a s a1 : Fin gc.configs.length)
    (ha1_succ : a1.val = a.val + 1)
    (has : a.val < s.val)
    (ha : gc.moverAt a = t) (hs : gc.moverAt s = t)
    (hno_t : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t)
    (ha1_left : gc.moverAt a1 = left t)
    (hifcL1 : gc.intervalFireCount (left t) a1.val s.val = 1)
    (hifcR0 : gc.intervalFireCount (right t) a1.val s.val = 0)
    (hlong : a1.val + 1 < s.val) :
    hasEntryConflict gc := by
  have ha1_nonmover : gc.moverAt a1 ≠ t := by
    exact hno_t a1 (by
      rw [ha1_succ]
      omega) (by omega)
  have ha1_nofire : ∀ k : Fin gc.configs.length,
      a1.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ t := by
    intro k hk1 hk2
    exact hno_t k (by
      rw [ha1_succ] at hk1
      omega) hk2
  let phase : TernaryPhase gc t :=
    { a := a1, s := s, ha_lt_s := by omega, hs_mover := hs,
      ha_nonmover := ha1_nonmover, ht_nofire := ha1_nofire }
  have hsum_eq1 :
      gc.intervalFireCount (left t) phase.a.val phase.s.val +
        gc.intervalFireCount (right t) phase.a.val phase.s.val = 1 := by
    simpa [phase, hifcL1, hifcR0]
  have hlen : phase.s.val > phase.a.val + 1 := by
    simpa [phase] using hlong
  exact one_sided_long_phase_ec gc t phase (Or.inl ha1_left) hsum_eq1 hlen

/-- From a global upper bound on first-neighbor fires, we can extract a
    consecutive linear `t`-pair with zero `right t` fires. This pair is either
    empty (`a+1 = s`) or yields explicit left-phase data after the first step. -/
private theorem zero_right_gap_empty_or_left_phase_of_neighbor_sum_le
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0)
    (hfc_t_ge2 : gc.fireCount t ≥ 2)
    (hfc_t_lt_L : gc.fireCount t < gc.configs.length)
    (hsum_le : gc.fireCount (left t) + gc.fireCount (right t) ≤ gc.fireCount t)
    (h_consec_le1 : ∀ (a s : Fin gc.configs.length),
      a.val < s.val →
      gc.moverAt a = t → gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      gc.intervalFireCount (left t) a.val s.val +
        gc.intervalFireCount (right t) a.val s.val ≤ 1) :
    ∃ (a s : Fin gc.configs.length),
      a.val < s.val ∧
      gc.moverAt a = t ∧
      gc.moverAt s = t ∧
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) ∧
      (a.val + 1 = s.val ∨
        ∃ a1 : Fin gc.configs.length,
          a1.val = a.val + 1 ∧
          gc.moverAt a1 = left t ∧
          gc.intervalFireCount (left t) a1.val s.val = 1 ∧
          gc.intervalFireCount (right t) a1.val s.val = 0) := by
  obtain ⟨a, s, has, ha, hs, hno_t, hifcR0⟩ :=
    exists_zero_right_gap_of_neighbor_sum_le gc t hbL hbR hfull hfc_t_ge2 hfc_t_lt_L hsum_le
  by_cases hgap : a.val + 1 < s.val
  · obtain ⟨ha1_left, hifcL1, hifcR1⟩ :=
      zero_right_gap_nonempty_gives_left_phase_data gc t a s has ha hs hno_t
        (h_consec_le1 a s has ha hs hno_t) hifcR0 hgap
    refine ⟨a, s, has, ha, hs, hno_t, Or.inr ?_⟩
    refine ⟨⟨a.val + 1, by
      have := s.isLt
      omega⟩, rfl, ha1_left, hifcL1, hifcR1⟩
  · refine ⟨a, s, has, ha, hs, hno_t, Or.inl ?_⟩
    omega

/-- If the cyclic wrap contribution of `left t` and `right t` is at most `1`,
    then the total first-neighbor fire count is at most `fireCount t`, provided
    `s_min` and `s_max` are the first and last linear `t`-fires. This isolates
    the remaining upper-bound problem to controlling the wrap contribution. -/
private theorem neighbor_sum_le_of_consec_and_wrap_le1_explicit
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hfc_t_ge2 : gc.fireCount t ≥ 2)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hs_min_fire : gc.moverAt s_min = t)
    (hs_max_fire : gc.moverAt s_max = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (h_consec_le1 : ∀ (a s : Fin gc.configs.length),
      a.val < s.val →
      gc.moverAt a = t → gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      gc.intervalFireCount (left t) a.val s.val +
        gc.intervalFireCount (right t) a.val s.val ≤ 1)
    (hwrap_le1 :
      gc.intervalFireCount (left t) 0 s_min.val +
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length +
        gc.intervalFireCount (right t) 0 s_min.val +
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length ≤ 1) :
    gc.fireCount (left t) + gc.fireCount (right t) ≤ gc.fireCount t := by
  have hinterior_le := ifc_sum_le_of_consec_le1 gc t (left t) (right t) h_consec_le1
    (s_max.val - s_min.val) s_min s_max le_rfl hs_lt hs_min_fire hs_max_fire
  have hinterior_eq :=
    t_fireCount_between_first_last gc t hfc_t_ge2 s_min s_max hs_lt hs_min_fire hs_max_fire
      hno_t_before hno_t_after
  have hfcL_eq := fireCount_eq_interior_plus_wrap_of_ne_t_explicit gc t (left t)
    s_min s_max hs_lt hs_max_fire (left_ne_self_nfec t)
  have hfcR_eq := fireCount_eq_interior_plus_wrap_of_ne_t_explicit gc t (right t)
    s_min s_max hs_lt hs_max_fire (right_ne_self_nfec t)
  rw [show gc.fireCount (left t) =
      gc.intervalFireCount (left t) s_min.val s_max.val +
        (gc.intervalFireCount (left t) 0 s_min.val +
          gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length) from hfcL_eq]
  rw [show gc.fireCount (right t) =
      gc.intervalFireCount (right t) s_min.val s_max.val +
        (gc.intervalFireCount (right t) 0 s_min.val +
          gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length) from hfcR_eq]
  rw [hinterior_eq] at hinterior_le
  have hwrap_total :
      (gc.intervalFireCount (left t) 0 s_min.val +
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length) +
      (gc.intervalFireCount (right t) 0 s_min.val +
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length) ≤ 1 := by
    omega
  calc
    (gc.intervalFireCount (left t) s_min.val s_max.val +
        (gc.intervalFireCount (left t) 0 s_min.val +
          gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length)) +
      (gc.intervalFireCount (right t) s_min.val s_max.val +
        (gc.intervalFireCount (right t) 0 s_min.val +
          gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length))
        = (gc.intervalFireCount (left t) s_min.val s_max.val +
            gc.intervalFireCount (right t) s_min.val s_max.val) +
          ((gc.intervalFireCount (left t) 0 s_min.val +
              gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length) +
            (gc.intervalFireCount (right t) 0 s_min.val +
              gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length)) := by
            omega
    _ ≤ gc.fireCount t := by
      omega

/-- Explicit wrap-bound version of
    `zero_right_gap_empty_or_left_phase_of_neighbor_sum_le`. This is the
    current global reduction target: once the wrap contribution is controlled,
    the residual is reduced to either an empty `t`-gap or explicit left-phase
    data. -/
private theorem zero_right_gap_empty_or_left_phase_of_wrap_bound_explicit
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0)
    (hfc_t_ge2 : gc.fireCount t ≥ 2)
    (hfc_t_lt_L : gc.fireCount t < gc.configs.length)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hs_min_fire : gc.moverAt s_min = t)
    (hs_max_fire : gc.moverAt s_max = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (h_consec_le1 : ∀ (a s : Fin gc.configs.length),
      a.val < s.val →
      gc.moverAt a = t → gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      gc.intervalFireCount (left t) a.val s.val +
        gc.intervalFireCount (right t) a.val s.val ≤ 1)
    (hwrap_le1 :
      gc.intervalFireCount (left t) 0 s_min.val +
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length +
        gc.intervalFireCount (right t) 0 s_min.val +
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length ≤ 1) :
    ∃ (a s : Fin gc.configs.length),
      a.val < s.val ∧
      gc.moverAt a = t ∧
      gc.moverAt s = t ∧
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) ∧
      (a.val + 1 = s.val ∨
        ∃ a1 : Fin gc.configs.length,
          a1.val = a.val + 1 ∧
          gc.moverAt a1 = left t ∧
          gc.intervalFireCount (left t) a1.val s.val = 1 ∧
          gc.intervalFireCount (right t) a1.val s.val = 0) := by
  have hsum_le := neighbor_sum_le_of_consec_and_wrap_le1_explicit gc t hfc_t_ge2
    s_min s_max hs_lt hs_min_fire hs_max_fire hno_t_before hno_t_after h_consec_le1 hwrap_le1
  exact zero_right_gap_empty_or_left_phase_of_neighbor_sum_le gc t hbL hbR hfull
    hfc_t_ge2 hfc_t_lt_L hsum_le h_consec_le1

/-- Auto-chosen `s_min` / `s_max` version of
    `zero_right_gap_empty_or_left_phase_of_wrap_bound_explicit`. -/
private theorem zero_right_gap_empty_or_left_phase_of_wrap_bound
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0)
    (hfc_t_ge2 : gc.fireCount t ≥ 2)
    (hfc_t_lt_L : gc.fireCount t < gc.configs.length)
    (h_consec_le1 : ∀ (a s : Fin gc.configs.length),
      a.val < s.val →
      gc.moverAt a = t → gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      gc.intervalFireCount (left t) a.val s.val +
        gc.intervalFireCount (right t) a.val s.val ≤ 1)
    (hwrap_le1 :
      let tFires : Finset (Fin gc.configs.length) :=
        Finset.univ.filter (fun k => gc.moverAt k = t)
      let s_min : Fin gc.configs.length := tFires.min' (by
        have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc_t_ge2
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
      let s_max : Fin gc.configs.length := tFires.max' (by
        have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc_t_ge2
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
      gc.intervalFireCount (left t) 0 s_min.val +
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length +
        gc.intervalFireCount (right t) 0 s_min.val +
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length ≤ 1) :
    ∃ (a s : Fin gc.configs.length),
      a.val < s.val ∧
      gc.moverAt a = t ∧
      gc.moverAt s = t ∧
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) ∧
      (a.val + 1 = s.val ∨
        ∃ a1 : Fin gc.configs.length,
          a1.val = a.val + 1 ∧
          gc.moverAt a1 = left t ∧
          gc.intervalFireCount (left t) a1.val s.val = 1 ∧
          gc.intervalFireCount (right t) a1.val s.val = 0) := by
  classical
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
      rw [← heq] at hle2
      exact le_antisymm hle2 hle1
    have hfc_le1 : gc.fireCount t ≤ 1 := by
      rw [gc.fireCount_eq_sum_moverAt t]
      have hbd : ∀ j : Fin gc.configs.length,
          (if gc.moverAt j = t then (1 : Nat) else 0) ≤
            (if j = s_min then 1 else 0) := by
        intro j
        by_cases hj : gc.moverAt j = t
        · rw [huniq j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)]
          simp [hs_min_fire]
        · simp [hj]
      calc ∑ j, (if gc.moverAt j = t then (1 : Nat) else 0)
          ≤ ∑ j, (if j = s_min then 1 else 0) :=
            Finset.sum_le_sum (fun j _ => hbd j)
        _ = 1 := by
          rw [Finset.sum_eq_single s_min
            (fun b _ hb => by simp [hb]) (by simp)]
          simp
    omega
  have hs_lt : s_min.val < s_max.val := by
    have hle : s_min ≤ s_max := Finset.min'_le tFires s_max (Finset.max'_mem tFires htFires_ne)
    exact lt_of_le_of_ne hle (fun h => hs_ne (Fin.ext h))
  have hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t := by
    intro k hk
    intro hfire
    have hk_mem : k ∈ tFires := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hfire⟩
    have := Finset.min'_le tFires k hk_mem
    omega
  have hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t := by
    intro k hk
    intro hfire
    have hk_mem : k ∈ tFires := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hfire⟩
    have := Finset.le_max' tFires k hk_mem
    omega
  exact zero_right_gap_empty_or_left_phase_of_wrap_bound_explicit gc t hbL hbR hfull
    hfc_t_ge2 hfc_t_lt_L s_min s_max hs_lt hs_min_fire hs_max_fire
    hno_t_before hno_t_after h_consec_le1 (by
      dsimp [tFires, s_min, s_max]
      exact hwrap_le1)

/-- Once the wrap contribution is bounded by `1`, the remaining proof only has
    to rule out the empty-gap and short-left-phase residues. The long left-phase
    branch is already discharged by `left_phase_data_long_ec`. -/
private theorem wrap_bound_reduction_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0)
    (hfc_t_ge2 : gc.fireCount t ≥ 2)
    (hfc_t_lt_L : gc.fireCount t < gc.configs.length)
    (h_consec_le1 : ∀ (a s : Fin gc.configs.length),
      a.val < s.val →
      gc.moverAt a = t → gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      gc.intervalFireCount (left t) a.val s.val +
        gc.intervalFireCount (right t) a.val s.val ≤ 1)
    (hwrap_le1 :
      let tFires : Finset (Fin gc.configs.length) :=
        Finset.univ.filter (fun k => gc.moverAt k = t)
      let s_min : Fin gc.configs.length := tFires.min' (by
        have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc_t_ge2
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
      let s_max : Fin gc.configs.length := tFires.max' (by
        have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc_t_ge2
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
      gc.intervalFireCount (left t) 0 s_min.val +
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length +
        gc.intervalFireCount (right t) 0 s_min.val +
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length ≤ 1)
    (hno_empty :
      ∀ (a s : Fin gc.configs.length),
        a.val < s.val →
        gc.moverAt a = t →
        gc.moverAt s = t →
        (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
        a.val + 1 = s.val →
        False)
    (hno_short_left :
      ∀ (a s a1 : Fin gc.configs.length),
        a.val < s.val →
        gc.moverAt a = t →
        gc.moverAt s = t →
        (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
        a1.val = a.val + 1 →
        gc.moverAt a1 = left t →
        gc.intervalFireCount (left t) a1.val s.val = 1 →
        gc.intervalFireCount (right t) a1.val s.val = 0 →
        ¬(a1.val + 1 < s.val) →
        False) :
    hasEntryConflict gc := by
  obtain ⟨a, s, has, ha, hs, hno_t, hres⟩ :=
    zero_right_gap_empty_or_left_phase_of_wrap_bound gc t hbL hbR hfull
      hfc_t_ge2 hfc_t_lt_L h_consec_le1 hwrap_le1
  rcases hres with hempty | ⟨a1, ha1_succ, ha1_left, hifcL1, hifcR0⟩
  · exact False.elim (hno_empty a s has ha hs hno_t hempty)
  · by_cases hlong : a1.val + 1 < s.val
    · exact left_phase_data_long_ec gc t a s a1 ha1_succ has ha hs hno_t
        ha1_left hifcL1 hifcR0 hlong
    · exact False.elim (hno_short_left a s a1 has ha hs hno_t
        ha1_succ ha1_left hifcL1 hifcR0 hlong)

/-- Final packaged residual after threading the wrap-bound reduction into the
    normal-form proof. The long left-phase branch is already eliminated, so the
    remaining work is exactly:
    1. force the cyclic wrap contribution down to `≤ 1`, where the only live
       wrap shapes left are tail-mixed or the explicit cross-boundary block;
    2. rule out the empty-gap and short-left residues extracted from the
       zero-`right t` gap reduction. -/
private theorem normalForm_tail_or_boundary_wrap_residual
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hfc2 : gc.fireCount t ≥ 2) :
    (let tFires : Finset (Fin gc.configs.length) :=
      Finset.univ.filter (fun k => gc.moverAt k = t)
    let s_min : Fin gc.configs.length := tFires.min' (by
      have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc2
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
    let s_max : Fin gc.configs.length := tFires.max' (by
      have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc2
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
    gc.intervalFireCount (left t) 0 s_min.val +
      gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length +
      gc.intervalFireCount (right t) 0 s_min.val +
      gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length ≤ 1) ∧
    (∀ (a s : Fin gc.configs.length),
      a.val < s.val →
      gc.moverAt a = t →
      gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      a.val + 1 = s.val →
      False) ∧
    (∀ (a s a1 : Fin gc.configs.length),
      a.val < s.val →
      gc.moverAt a = t →
      gc.moverAt s = t →
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) →
      a1.val = a.val + 1 →
      gc.moverAt a1 = left t →
      gc.intervalFireCount (left t) a1.val s.val = 1 →
      gc.intervalFireCount (right t) a1.val s.val = 0 →
      ¬(a1.val + 1 < s.val) →
      False) := by
  -- Remaining blocker:
  -- 1. prove the cyclic wrap contribution is at most `1`
  --    Equivalently: if the wrap contribution is `≥ 2`, the helper layer
  --    now reduces it all the way to a genuinely cyclic mixed-wrap residue.
  --    More precisely:
  --    - both-even wrap is discharged
  --    - odd one-sided wrap is discharged on both sides
  --    - head-mixed wrap is discharged
  --    - the remaining wrap residue is tail-mixed or pure cross-boundary mixed
  -- 2. rule out the two small residues after the wrap reduction:
  --    (a) empty consecutive `t`-gap
  --    (b) short left-phase residue
  sorry

private theorem normalForm_sparse_phase_false
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (_hmt : sys.rs.m t ≥ 3)
    (hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0)
    (hfc2 : gc.fireCount t ≥ 2)
    (hfc_lt : gc.fireCount t < gc.configs.length)
    (hall_normal : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase) :
    hasEntryConflict gc := by
  by_contra hnoEC
  -- Step 1: Each proper TernaryPhase with ha_adj has J+K ≤ 1.
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
    by_cases hJ0 : J = 0
    · have : K = 1 := hconstraint.1 hJ0; omega
    by_cases hK0 : K = 0
    · have : J = 1 := hconstraint.2.1 hK0; omega
    exact hnoEC (mixed_phase_ec gc hn t hbL hbR phase ha_adj
      (Nat.pos_of_ne_zero hJ0) (Nat.pos_of_ne_zero hK0))
  have h_consec_le1 := consecutive_tpair_sum_le1_of_phase_bound gc t h_phase_le1
  have hwrap_reduction :
      (let tFires : Finset (Fin gc.configs.length) :=
        Finset.univ.filter (fun k => gc.moverAt k = t)
      let s_min : Fin gc.configs.length := tFires.min' (by
        have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc2
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
      let s_max : Fin gc.configs.length := tFires.max' (by
        have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc2
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
      gc.intervalFireCount (left t) 0 s_min.val +
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length +
        gc.intervalFireCount (right t) 0 s_min.val +
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length ≤ 1) →
      ∃ (a s : Fin gc.configs.length),
        a.val < s.val ∧
        gc.moverAt a = t ∧
        gc.moverAt s = t ∧
        (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) ∧
        (a.val + 1 = s.val ∨
          ∃ a1 : Fin gc.configs.length,
            a1.val = a.val + 1 ∧
            gc.moverAt a1 = left t ∧
            gc.intervalFireCount (left t) a1.val s.val = 1 ∧
            gc.intervalFireCount (right t) a1.val s.val = 0) := by
    intro hwrap_le1
    exact zero_right_gap_empty_or_left_phase_of_wrap_bound gc t hbL hbR hfull
      hfc2 hfc_lt h_consec_le1 hwrap_le1
  have hwrap_reduction_long :
      (let tFires : Finset (Fin gc.configs.length) :=
        Finset.univ.filter (fun k => gc.moverAt k = t)
      let s_min : Fin gc.configs.length := tFires.min' (by
        have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc2
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
      let s_max : Fin gc.configs.length := tFires.max' (by
        have ⟨a, _, _, ha, _⟩ := exists_two_fire_steps_of_ge2 gc t hfc2
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)
      gc.intervalFireCount (left t) 0 s_min.val +
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length +
        gc.intervalFireCount (right t) 0 s_min.val +
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length ≤ 1) →
      (∃ (a s a1 : Fin gc.configs.length),
        a.val < s.val ∧
        gc.moverAt a = t ∧
        gc.moverAt s = t ∧
        (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) ∧
        a1.val = a.val + 1 ∧
        gc.moverAt a1 = left t ∧
        gc.intervalFireCount (left t) a1.val s.val = 1 ∧
        gc.intervalFireCount (right t) a1.val s.val = 0 ∧
        a1.val + 1 < s.val) →
      hasEntryConflict gc := by
    intro _ hlong
    rcases hlong with ⟨a, s, a1, has, ha, hs, hno_t, ha1_succ, ha1_left, hifcL1, hifcR0, ha1_long⟩
    exact left_phase_data_long_ec gc t a s a1 ha1_succ has ha hs hno_t
      ha1_left hifcL1 hifcR0 ha1_long
  have hresidual := normalForm_tail_or_boundary_wrap_residual gc t hfc2
  exact hnoEC <| wrap_bound_reduction_ec gc t hbL hbR hfull hfc2 hfc_lt h_consec_le1
    hresidual.1 hresidual.2.1 hresidual.2.2

/-! ### Main theorem -/

/-- **NormalForm gives entry conflict.**

    Given a sandwiched ternary processor t (both neighbors binary) where
    all TernaryPhases are in normalForm and n ≥ 9, derive hasEntryConflict.

    No callbacks. This theorem is called directly by ZeroWinding, Sweep,
    and OddWinding when their phase dispatch leaves the normalForm residual. -/
theorem normalForm_gives_ec
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (hmt : sys.rs.m t ≥ 3)
    (hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0)
    (hfc2 : gc.fireCount t ≥ 2)
    (hfc_lt : gc.fireCount t < gc.configs.length)
    (hall_normal : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase) :
    hasEntryConflict gc :=
  normalForm_sparse_phase_false gc hn t hbL hbR hmt hfull hfc2 hfc_lt hall_normal

end LeanMn
