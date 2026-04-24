/-
  Theorem.lean — Shadow Cycle Mirror Theorem (Phase 6, Claim 4.4.1)

  Main theorem: for any uniform sweep good cycle on a ring with ≥ 3 binary
  processors, there exists a shadow trap of length 2n. Combined with
  shadowTrap_not_converges, this proves ¬converges.

  The proof assembles the 5 shadow properties:
    (i)   Closure: s_k → s_{k+1} via mover entry
    (ii)  Movers: mover at step k is σ(k mod n)
    (iii) Distinctness: all 2n shadow configs are distinct
    (iv)  Disjointness: shadow ∩ good = ∅
    (v)   Single privileged: each shadow config has exactly one privileged proc
-/
import LeanMn.LowerBound.MNU
import LeanMn.LowerBound.Shadow.Construction

namespace LeanMn

variable {sys : System}

/-! ### Shadow closure infrastructure -/

-- When (k + d) % (2n) is not at a boundary {0, n}, the active status
-- is preserved from step k to step k+1.
-- Helper: ((k+1) % (2n) + d) % (2n) = ((k+d) % (2n) + 1) % (2n)
private lemma mod_shift_eq (n k d : Nat) (hn : 0 < n) :
    ((k + 1) % (2 * n) + d) % (2 * n) = ((k + d) % (2 * n) + 1) % (2 * n) := by
  have h2n : 0 < 2 * n := by omega
  -- Both sides equal (k + d + 1) % (2n)
  suffices h1 : ((k + 1) % (2 * n) + d) % (2 * n) = (k + d + 1) % (2 * n) by
    suffices h2 : ((k + d) % (2 * n) + 1) % (2 * n) = (k + d + 1) % (2 * n) by
      rw [h1, h2]
    have hmod2 := Nat.div_add_mod (k + d) (2 * n)
    conv_rhs => rw [show k + d + 1 = (k + d) % (2 * n) + 1 +
      (k + d) / (2 * n) * (2 * n) from by linarith]
    rw [Nat.add_mul_mod_self_right]
  have hmod1 := Nat.div_add_mod (k + 1) (2 * n)
  conv_rhs => rw [show k + d + 1 = (k + 1) % (2 * n) + d +
    (k + 1) / (2 * n) * (2 * n) from by linarith]
  rw [Nat.add_mul_mod_self_right]

private lemma shadow_active_stable (n k d : Nat) (hn : 1 ≤ n) (_hk : k < 2 * n)
    (h_ne0 : (k + d) % (2 * n) ≠ 0)
    (h_neN : (k + d) % (2 * n) ≠ n) :
    (1 ≤ (k + d) % (2 * n) ∧ (k + d) % (2 * n) ≤ n) ↔
    (1 ≤ ((k + 1) % (2 * n) + d) % (2 * n) ∧
     ((k + 1) % (2 * n) + d) % (2 * n) ≤ n) := by
  have h2n_pos : 0 < 2 * n := by omega
  have hr_lt : (k + d) % (2 * n) < 2 * n := Nat.mod_lt _ h2n_pos
  rw [mod_shift_eq n k d (by omega)]
  -- Now: (k+d)%(2n) ∈ [1,n] ↔ ((k+d)%(2n)+1)%(2n) ∈ [1,n], given ≠ 0, ≠ n
  by_cases hr_last : (k + d) % (2 * n) = 2 * n - 1
  · rw [hr_last, show 2 * n - 1 + 1 = 2 * n from by omega, Nat.mod_self]
    constructor <;> intro ⟨h1, h2⟩ <;> omega
  · rw [Nat.mod_eq_of_lt (by omega : (k + d) % (2 * n) + 1 < 2 * n)]
    constructor <;> intro ⟨h1, h2⟩ <;> (constructor <;> omega)

-- Helper: if two values are both in {highVal i, 0} and have the same
-- active status, they are equal.
private lemma shadow_val_eq_ite {mi : Nat} (_hmi : 2 ≤ mi) (v : Fin mi)
    (_hv_pos : v.val ≠ 0)
    (c1 c2 : Prop) [Decidable c1] [Decidable c2] (hiff : c1 ↔ c2) :
    (if c1 then v else (⟨0, by omega⟩ : Fin mi)) =
    (if c2 then v else ⟨0, by omega⟩) := by
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · rfl

private lemma canonicalShadowConfig_off_mover_eq
    (wc : WaterfallCycle sys) (hn : 5 ≤ sys.rs.n)
    (k : Fin (2 * sys.rs.n)) (q : Fin sys.rs.n)
    (hq : q ≠ shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩) :
    canonicalShadowConfig wc
        ⟨(k.val + 1) % (2 * sys.rs.n), Nat.mod_lt _ (by omega)⟩ q =
      canonicalShadowConfig wc k q := by
  have hnbound :=
    shadow_off_boundary_of_ne_perm sys.rs.n hn k.val k.isLt q hq
  have hiff :
      shadowActive sys.rs.n k.val (shadowShift sys.rs.n q) ↔
        shadowActive sys.rs.n ((k.val + 1) % (2 * sys.rs.n)) (shadowShift sys.rs.n q) := by
    simpa [shadowActive] using
      (shadow_active_stable sys.rs.n k.val (shadowShift sys.rs.n q)
        (by omega) k.isLt hnbound.1 hnbound.2)
  symm
  simpa [canonicalShadowConfig] using
    shadow_val_eq_ite (sys.rs.m_pos q) (wc.highVal q) (wc.highVal_pos q)
      (shadowActive sys.rs.n k.val (shadowShift sys.rs.n q))
      (shadowActive sys.rs.n ((k.val + 1) % (2 * sys.rs.n)) (shadowShift sys.rs.n q))
      hiff

theorem canonicalShadowClosure_of_entryCore
    (wc : WaterfallCycle sys) (hn : 5 ≤ sys.rs.n)
    (hentry :
      ∀ k : Fin (2 * sys.rs.n),
        let p : Fin sys.rs.n :=
          shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
        privileged sys (canonicalShadowConfig wc k) p ∧
          canonicalShadowConfig wc
            ⟨(k.val + 1) % (2 * sys.rs.n), Nat.mod_lt _ (by omega)⟩ p =
              move sys (canonicalShadowConfig wc k) p p) :
    shadowClosure (canonicalShadowConstruction wc) := by
  intro k
  let p : Fin sys.rs.n :=
    shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
  refine ⟨p, ?_, ?_⟩
  · simpa [p, canonicalShadowConstruction] using (hentry k).1
  · funext q
    by_cases hq : q = p
    · subst hq
      simpa [p, canonicalShadowConstruction] using (hentry k).2
    · have hfix := canonicalShadowConfig_off_mover_eq wc hn k q hq
      simpa [p, canonicalShadowConstruction, move, hq] using hfix

private def shadowMatchIndex
    (wc : WaterfallCycle sys) (hn : 5 ≤ sys.rs.n) (k : Fin (2 * sys.rs.n)) :
    Fin wc.configs.length :=
  let p : Fin sys.rs.n :=
    shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
  ⟨p.val + if shadowActive sys.rs.n k.val (shadowShift sys.rs.n p) then sys.rs.n else 0, by
    have hlen : wc.configs.length = 2 * sys.rs.n := wc.len_eq
    by_cases hact : shadowActive sys.rs.n k.val (shadowShift sys.rs.n p)
    · simpa [hlen, hact] using (show p.val + sys.rs.n < 2 * sys.rs.n by omega)
    · simpa [hlen, hact] using (show p.val < 2 * sys.rs.n by omega)⟩

private lemma shadowMatchIndex_moverAt
    (wc : WaterfallCycle sys) (hn : 5 ≤ sys.rs.n) (k : Fin (2 * sys.rs.n)) :
    wc.toGoodCycle.moverAt (shadowMatchIndex wc hn k) =
      shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩ := by
  let p : Fin sys.rs.n :=
    shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
  have hm := waterfall_moverAt_eq wc (shadowMatchIndex wc hn k)
  apply Fin.ext
  have hmod0 :
      ((p.val + if shadowActive sys.rs.n k.val (shadowShift sys.rs.n p)
          then sys.rs.n else 0) % sys.rs.n) = p.val := by
    by_cases hact : shadowActive sys.rs.n k.val
        (shadowShift sys.rs.n p)
    · rw [if_pos hact]
      rw [show p.val + sys.rs.n = p.val + 1 * sys.rs.n from by omega,
        Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt p.isLt
    · rw [if_neg hact]
      exact Nat.mod_eq_of_lt p.isLt
  have hmod : (shadowMatchIndex wc hn k).val % sys.rs.n = p.val := by
    simpa [shadowMatchIndex, p] using hmod0
  simpa [hmod, p] using congrArg Fin.val hm

private lemma left_val_eq_last_of_val_zero {n : Nat} (i : Fin n)
    (h : i.val = 0) :
    (left i).val = n - 1 := by
  rw [left_val, h, Nat.zero_add]
  exact Nat.mod_eq_of_lt (by
    have hi := i.isLt
    omega)

private lemma left_val_eq_pred_of_val_ne_zero {n : Nat} (i : Fin n)
    (h : i.val ≠ 0) :
    (left i).val = i.val - 1 := by
  rw [left_val, show i.val + n - 1 = (i.val - 1) + n by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private lemma right_val_eq_zero_of_val_last {n : Nat} (i : Fin n)
    (h : i.val = n - 1) :
    (right i).val = 0 := by
  rw [right_val, h, show n - 1 + 1 = n by omega, Nat.mod_self]

private lemma right_val_eq_succ_of_val_ne_last {n : Nat} (i : Fin n)
    (h : i.val ≠ n - 1) :
    (right i).val = i.val + 1 := by
  rw [right_val, Nat.mod_eq_of_lt]
  omega

private lemma shadowMatchIndex_left_waterfall_active
    (wc : WaterfallCycle sys) (hn : 5 ≤ sys.rs.n) (k : Fin (2 * sys.rs.n)) :
    let p : Fin sys.rs.n :=
      shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
    let a := shadowActive sys.rs.n k.val (shadowShift sys.rs.n p)
    let j := shadowMatchIndex wc hn k
    (1 ≤ (j.val + 2 * sys.rs.n - (left p).val) % (2 * sys.rs.n) ∧
        (j.val + 2 * sys.rs.n - (left p).val) % (2 * sys.rs.n) ≤ sys.rs.n) ↔
      (a ↔ p.val = 0) := by
  dsimp
  let p : Fin sys.rs.n :=
    shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
  let a : Prop := shadowActive sys.rs.n k.val (shadowShift sys.rs.n p)
  have hw :=
    waterfall_active_iff sys.rs.n (shadowMatchIndex wc hn k).val (left p).val hn
      (by simpa [wc.len_eq] using (shadowMatchIndex wc hn k).isLt)
      (left p).isLt
  have hw' :
      (1 ≤ ((p.val + if a then sys.rs.n else 0) + 2 * sys.rs.n - (left p).val) % (2 * sys.rs.n) ∧
          ((p.val + if a then sys.rs.n else 0) + 2 * sys.rs.n - (left p).val) % (2 * sys.rs.n) ≤ sys.rs.n) ↔
        ((left p).val + 1 ≤ p.val + (if a then sys.rs.n else 0) ∧
          p.val + (if a then sys.rs.n else 0) ≤ (left p).val + sys.rs.n) := by
    simpa [p, a, shadowMatchIndex] using hw
  change
    (1 ≤ ((p.val + (if a then sys.rs.n else 0)) + 2 * sys.rs.n - (left p).val) % (2 * sys.rs.n) ∧
        ((p.val + (if a then sys.rs.n else 0)) + 2 * sys.rs.n - (left p).val) % (2 * sys.rs.n) ≤ sys.rs.n) ↔
      (a ↔ p.val = 0)
  rw [hw']
  by_cases hp0 : p.val = 0
  · rw [left_val_eq_last_of_val_zero p hp0]
    by_cases hact : a
    · simp [hact, hp0]
      omega
    · simp [hact, hp0]
  · rw [left_val_eq_pred_of_val_ne_zero p hp0]
    by_cases hact : a
    · simp [hact, hp0]
      omega
    · simp [hact, hp0]
      omega

private lemma shadowMatchIndex_right_waterfall_active
    (wc : WaterfallCycle sys) (hn : 5 ≤ sys.rs.n) (k : Fin (2 * sys.rs.n)) :
    let p : Fin sys.rs.n :=
      shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
    let a := shadowActive sys.rs.n k.val (shadowShift sys.rs.n p)
    let j := shadowMatchIndex wc hn k
    (1 ≤ (j.val + 2 * sys.rs.n - (right p).val) % (2 * sys.rs.n) ∧
        (j.val + 2 * sys.rs.n - (right p).val) % (2 * sys.rs.n) ≤ sys.rs.n) ↔
      (a ↔ p.val ≠ sys.rs.n - 1) := by
  dsimp
  let p : Fin sys.rs.n :=
    shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
  let a : Prop := shadowActive sys.rs.n k.val (shadowShift sys.rs.n p)
  have hw :=
    waterfall_active_iff sys.rs.n (shadowMatchIndex wc hn k).val (right p).val hn
      (by simpa [wc.len_eq] using (shadowMatchIndex wc hn k).isLt)
      (right p).isLt
  have hw' :
      (1 ≤ ((p.val + if a then sys.rs.n else 0) + 2 * sys.rs.n - (right p).val) % (2 * sys.rs.n) ∧
          ((p.val + if a then sys.rs.n else 0) + 2 * sys.rs.n - (right p).val) % (2 * sys.rs.n) ≤ sys.rs.n) ↔
        ((right p).val + 1 ≤ p.val + (if a then sys.rs.n else 0) ∧
          p.val + (if a then sys.rs.n else 0) ≤ (right p).val + sys.rs.n) := by
    simpa [p, a, shadowMatchIndex] using hw
  change
    (1 ≤ ((p.val + (if a then sys.rs.n else 0)) + 2 * sys.rs.n - (right p).val) % (2 * sys.rs.n) ∧
        ((p.val + (if a then sys.rs.n else 0)) + 2 * sys.rs.n - (right p).val) % (2 * sys.rs.n) ≤ sys.rs.n) ↔
      (a ↔ p.val ≠ sys.rs.n - 1)
  rw [hw']
  by_cases hplast : p.val = sys.rs.n - 1
  · rw [right_val_eq_zero_of_val_last p hplast]
    by_cases hact : a
    · simp [hact, hplast]
      omega
    · simp [hact, hplast]
      omega
  · rw [right_val_eq_succ_of_val_ne_last p hplast]
    by_cases hact : a
    · simp [hact, hplast]
      omega
    · simp [hact, hplast]

private lemma lt_two_mul_decompose_mod_local (n k : Nat) (_hn : 0 < n) (hk : k < 2 * n) :
    k = k % n ∨ k = k % n + n := by
  by_cases hkn : k < n
  · left
    symm
    exact Nat.mod_eq_of_lt hkn
  · right
    have hge : n ≤ k := by omega
    have hlt : k - n < n := by omega
    have hmod : k % n = k - n := by
      rw [Nat.mod_eq_sub_mod hge]
      simpa [Nat.mod_eq_of_lt hlt]
    omega

private lemma mod_two_period_boundary_local (n k : Nat) (hn : 0 < n) (hk : k < 2 * n) :
    (k < n ∧ k = k % n) ∨ (n ≤ k ∧ k = k % n + n) := by
  rcases lt_two_mul_decompose_mod_local n k hn hk with hkmod | hkmod
  · exact Or.inl ⟨by
      rw [hkmod]
      exact Nat.mod_lt _ hn, hkmod⟩
  · exact Or.inr ⟨by omega, hkmod⟩

private lemma mod_add_period_local (n a : Nat) (hn : 0 < n) (ha : a < n) :
    (a + n) % n = a := by
  rw [show a + n = a + 1 * n by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]

private lemma shadow_left_first_half_active
    (n : Nat) (hn : 5 ≤ n) (r : Nat) (hr : r < n) :
    let p : Fin n := shadowPerm n hn ⟨r, hr⟩
    let a := shadowActive n r (shadowShift n p)
    shadowActive n r (shadowShift n (left p)) ↔ (a ↔ p.val = 0) := by
  dsimp
  by_cases h0 : r = 0
  · subst h0
    have hleft :
        left (⟨n - 4, by omega⟩ : Fin n) = ⟨n - 5, by omega⟩ := by
      apply Fin.ext
      simpa using left_val_eq_pred_of_val_ne_zero
        (⟨n - 4, by omega⟩ : Fin n)
        (Nat.sub_ne_zero_of_lt (by omega))
    rw [shadowPerm_zero n hn, hleft]
    have ha : ¬ shadowActive n 0 (shadowShift n ⟨n - 4, by omega⟩) := by
      rw [show shadowActive n 0 (shadowShift n ⟨n - 4, by omega⟩) ↔
            (1 ≤ 0 ∧ 0 ≤ n) by
            simpa [shadowActive] using shadow_n4_active n 0 hn (by omega)]
      omega
    have hleftAct : shadowActive n 0 (shadowShift n ⟨n - 5, by omega⟩) := by
      rw [shadowShift_linear n hn (n - 5) (by omega)]
      unfold shadowActive
      rw [Nat.mod_eq_of_lt (by omega)]
      constructor <;> omega
    have hp0 : (n - 4 : Nat) ≠ 0 := by omega
    simp [ha, hleftAct, hp0]
  · by_cases h1 : r = 1
    · subst h1
      have hleft :
          left (⟨n - 1, by omega⟩ : Fin n) = ⟨n - 2, by omega⟩ := by
        apply Fin.ext
        simpa using left_val_eq_pred_of_val_ne_zero
          (⟨n - 1, by omega⟩ : Fin n)
          (Nat.sub_ne_zero_of_lt (by omega))
      rw [shadowPerm_one n hn, hleft]
      have ha : ¬ shadowActive n 1 (shadowShift n ⟨n - 1, by omega⟩) := by
        rw [show shadowActive n 1 (shadowShift n ⟨n - 1, by omega⟩) ↔
              (2 ≤ 1 ∧ 1 ≤ n + 1) by
              simpa [shadowActive] using shadow_n1_active n 1 hn (by omega)]
        omega
      have hleftAct : shadowActive n 1 (shadowShift n ⟨n - 2, by omega⟩) := by
        rw [show shadowActive n 1 (shadowShift n ⟨n - 2, by omega⟩) ↔
              (1 ≤ n - 2 ∨ 1 = 2 * n - 1) by
              simpa [shadowActive] using shadow_n2_active n 1 hn (by omega)]
        exact Or.inl (by omega)
      have hp0 : (n - 1 : Nat) ≠ 0 := by omega
      simp [ha, hleftAct, hp0]
    · by_cases h2 : r = 2
      · subst h2
        have hleft :
            left (⟨0, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
          apply Fin.ext
          simpa using left_val_eq_last_of_val_zero
            (⟨0, by omega⟩ : Fin n) rfl
        rw [shadowPerm_two n hn, hleft]
        have ha : shadowActive n 2 (shadowShift n ⟨0, by omega⟩) := by
          exact (linear_shift_lower n 2 0 hn (by omega) (by omega) (by omega)).2
            (by omega)
        have hleftAct : shadowActive n 2 (shadowShift n ⟨n - 1, by omega⟩) := by
          rw [show shadowActive n 2 (shadowShift n ⟨n - 1, by omega⟩) ↔
                (2 ≤ 2 ∧ 2 ≤ n + 1) by
                simpa [shadowActive] using shadow_n1_active n 2 hn (by omega)]
          constructor <;> omega
        simp [ha, hleftAct]
      · by_cases hmid : r ≤ n - 3
        · have hr3 : 3 ≤ r := by omega
          have hleft :
              left (⟨r - 2, by omega⟩ : Fin n) = ⟨r - 3, by omega⟩ := by
            apply Fin.ext
            simpa using left_val_eq_pred_of_val_ne_zero
              (⟨r - 2, by omega⟩ : Fin n)
              (Nat.sub_ne_zero_of_lt (by omega))
          rw [shadowPerm_mid n hn r hr3 hmid, hleft]
          have ha : shadowActive n r (shadowShift n ⟨r - 2, by omega⟩) := by
            exact (linear_shift_lower n r (r - 2) hn (by omega) (by omega) (by omega)).2
              (by omega)
          have hleftAct : ¬ shadowActive n r (shadowShift n ⟨r - 3, by omega⟩) := by
            intro h
            have := (linear_shift_lower n r (r - 3) hn (by omega) (by omega) (by omega)).1 h
            omega
          have hp0 : (r - 2 : Nat) ≠ 0 := by omega
          simp [ha, hleftAct, hp0]
        · by_cases hn2 : r = n - 2
          · subst hn2
            have hleft :
                left (⟨n - 2, by omega⟩ : Fin n) = ⟨n - 3, by omega⟩ := by
              apply Fin.ext
              simpa using left_val_eq_pred_of_val_ne_zero
                (⟨n - 2, by omega⟩ : Fin n)
                (Nat.sub_ne_zero_of_lt (by omega))
            rw [shadowPerm_n_sub_two n hn, hleft]
            have ha : shadowActive n (n - 2) (shadowShift n ⟨n - 2, by omega⟩) := by
              rw [show shadowActive n (n - 2) (shadowShift n ⟨n - 2, by omega⟩) ↔
                    (n - 2 ≤ n - 2 ∨ n - 2 = 2 * n - 1) by
                    simpa [shadowActive] using shadow_n2_active n (n - 2) hn (by omega)]
              exact Or.inl (by omega)
            have hleftAct : ¬ shadowActive n (n - 2) (shadowShift n ⟨n - 3, by omega⟩) := by
              rw [show shadowActive n (n - 2) (shadowShift n ⟨n - 3, by omega⟩) ↔
                    n ≤ n - 2 by
                    simpa [shadowActive] using shadow_n3_active n (n - 2) hn (by omega)]
              omega
            have hp0 : (n - 2 : Nat) ≠ 0 := by omega
            simp [ha, hleftAct, hp0]
          · have hlast : r = n - 1 := by omega
            subst hlast
            have hleft :
                left (⟨n - 3, by omega⟩ : Fin n) = ⟨n - 4, by omega⟩ := by
              apply Fin.ext
              simpa using left_val_eq_pred_of_val_ne_zero
                (⟨n - 3, by omega⟩ : Fin n)
                (Nat.sub_ne_zero_of_lt (by omega))
            rw [shadowPerm_n_sub_one n hn, hleft]
            have ha : ¬ shadowActive n (n - 1) (shadowShift n ⟨n - 3, by omega⟩) := by
              rw [show shadowActive n (n - 1) (shadowShift n ⟨n - 3, by omega⟩) ↔
                    n ≤ n - 1 by
                    simpa [shadowActive] using shadow_n3_active n (n - 1) hn (by omega)]
              omega
            have hleftAct : shadowActive n (n - 1) (shadowShift n ⟨n - 4, by omega⟩) := by
              rw [show shadowActive n (n - 1) (shadowShift n ⟨n - 4, by omega⟩) ↔
                    (1 ≤ n - 1 ∧ n - 1 ≤ n) by
                    simpa [shadowActive] using shadow_n4_active n (n - 1) hn (by omega)]
              omega
            have hp0 : (n - 3 : Nat) ≠ 0 := by omega
            simp [ha, hleftAct, hp0]

private lemma shadow_left_active
    (n : Nat) (hn : 5 ≤ n) (k : Fin (2 * n)) :
    let p : Fin n := shadowPerm n hn ⟨k.val % n, Nat.mod_lt _ (by omega)⟩
    let a := shadowActive n k.val (shadowShift n p)
    shadowActive n k.val (shadowShift n (left p)) ↔ (a ↔ p.val = 0) := by
  let r : Nat := k.val % n
  let p : Fin n := shadowPerm n hn ⟨r, Nat.mod_lt _ (by omega)⟩
  have hr : r < n := by
    dsimp [r]
    exact Nat.mod_lt _ (by omega)
  rcases mod_two_period_boundary_local n k.val (by omega) k.isLt with ⟨_, hk_eq⟩ | ⟨_, hk_eq⟩
  · have hk_eq' : k.val = r := by
      simpa [r] using hk_eq
    rw [hk_eq']
    simpa [r, p] using shadow_left_first_half_active n hn r hr
  · have hk_eq' : k.val = r + n := by
      simpa [r] using hk_eq
    rw [hk_eq']
    have hrmod : (r + n) % n = r := mod_add_period_local n r (by omega) hr
    have hrself : r % n = r := Nat.mod_eq_of_lt hr
    have hp :
        shadowPerm n hn ⟨(r + n) % n, Nat.mod_lt _ (by omega)⟩ = p := by
      apply Fin.ext
      simpa [p, hrmod]
    have hbase :
        shadowActive n r (shadowShift n (left p)) ↔
          (shadowActive n r (shadowShift n p) ↔ p.val = 0) := by
      simpa [r, p] using shadow_left_first_half_active n hn r hr
    have hLflip :
        shadowActive n (r + n) (shadowShift n (left p)) ↔
          ¬ shadowActive n r (shadowShift n (left p)) :=
      shadowActive_add_n_iff_not n r (shadowShift n (left p)) (by omega)
    have hAflip :
        shadowActive n (r + n) (shadowShift n p) ↔
          ¬ shadowActive n r (shadowShift n p) :=
      shadowActive_add_n_iff_not n r (shadowShift n p) (by omega)
    by_cases hp0 : p.val = 0
    · have hbase' :
          shadowActive n r (shadowShift n (left p)) ↔
            shadowActive n r (shadowShift n p) := by
        simpa [hp0] using hbase
      have hgoal :
          shadowActive n (r + n) (shadowShift n (left p)) ↔
            shadowActive n (r + n) (shadowShift n p) := by
        calc
          shadowActive n (r + n) (shadowShift n (left p))
              ↔ ¬ shadowActive n r (shadowShift n (left p)) := hLflip
          _ ↔ ¬ shadowActive n r (shadowShift n p) := by simpa [hbase']
          _ ↔ shadowActive n (r + n) (shadowShift n p) := hAflip.symm
      simpa [hp0, p, hp, hrself] using hgoal
    · have hbase' :
          shadowActive n r (shadowShift n (left p)) ↔
            ¬ shadowActive n r (shadowShift n p) := by
        simpa [hp0] using hbase
      have hgoal :
          shadowActive n (r + n) (shadowShift n (left p)) ↔
            ¬ shadowActive n (r + n) (shadowShift n p) := by
        calc
          shadowActive n (r + n) (shadowShift n (left p))
              ↔ ¬ shadowActive n r (shadowShift n (left p)) := hLflip
          _ ↔ ¬¬ shadowActive n r (shadowShift n p) := by simpa [hbase']
          _ ↔ ¬ shadowActive n (r + n) (shadowShift n p) := by
                simpa using (not_congr hAflip).symm
      simpa [hp0, p, hp, hrself] using hgoal

private lemma shadow_right_first_half_active
    (n : Nat) (hn : 5 ≤ n) (r : Nat) (hr : r < n) :
    let p : Fin n := shadowPerm n hn ⟨r, hr⟩
    let a := shadowActive n r (shadowShift n p)
    shadowActive n r (shadowShift n (right p)) ↔ (a ↔ p.val ≠ n - 1) := by
  dsimp
  by_cases h0 : r = 0
  · subst h0
    have hright :
        right (⟨n - 4, by omega⟩ : Fin n) = ⟨n - 3, by omega⟩ := by
      have hi : (⟨n - 4, by omega⟩ : Fin n).val ≠ n - 1 := by
        simpa using (show n - 4 ≠ n - 1 by omega)
      have hval : (right (⟨n - 4, by omega⟩ : Fin n)).val = n - 4 + 1 := by
        simpa using right_val_eq_succ_of_val_ne_last
          (⟨n - 4, by omega⟩ : Fin n) hi
      apply Fin.ext
      calc
        (right (⟨n - 4, by omega⟩ : Fin n)).val = n - 4 + 1 := hval
        _ = n - 3 := by omega
    rw [shadowPerm_zero n hn, hright]
    have ha : ¬ shadowActive n 0 (shadowShift n ⟨n - 4, by omega⟩) := by
      rw [show shadowActive n 0 (shadowShift n ⟨n - 4, by omega⟩) ↔
            (1 ≤ 0 ∧ 0 ≤ n) by
            simpa [shadowActive] using shadow_n4_active n 0 hn (by omega)]
      omega
    have hrightAct : ¬ shadowActive n 0 (shadowShift n ⟨n - 3, by omega⟩) := by
      rw [show shadowActive n 0 (shadowShift n ⟨n - 3, by omega⟩) ↔
            n ≤ 0 by
            simpa [shadowActive] using shadow_n3_active n 0 hn (by omega)]
      omega
    have hplast : (n - 4 : Nat) ≠ n - 1 := Nat.ne_of_lt (by omega)
    simp [ha, hrightAct, hplast]
  · by_cases h1 : r = 1
    · subst h1
      have hright :
          right (⟨n - 1, by omega⟩ : Fin n) = ⟨0, by omega⟩ := by
        apply Fin.ext
        simpa using right_val_eq_zero_of_val_last
          (⟨n - 1, by omega⟩ : Fin n) rfl
      rw [shadowPerm_one n hn, hright]
      have ha : ¬ shadowActive n 1 (shadowShift n ⟨n - 1, by omega⟩) := by
        rw [show shadowActive n 1 (shadowShift n ⟨n - 1, by omega⟩) ↔
              (2 ≤ 1 ∧ 1 ≤ n + 1) by
              simpa [shadowActive] using shadow_n1_active n 1 hn (by omega)]
        omega
      have hrightAct : shadowActive n 1 (shadowShift n ⟨0, by omega⟩) := by
        rw [shadowShift_linear n hn 0 (by omega)]
        unfold shadowActive
        rw [Nat.mod_eq_of_lt (by omega)]
        constructor <;> omega
      simp [ha, hrightAct]
    · by_cases h2 : r = 2
      · subst h2
        have hright :
            right (⟨0, by omega⟩ : Fin n) = ⟨1, by omega⟩ := by
          have hi : (⟨0, by omega⟩ : Fin n).val ≠ n - 1 := by
            simpa using (show (0 : Nat) ≠ n - 1 by omega)
          apply Fin.ext
          simpa using right_val_eq_succ_of_val_ne_last
            (⟨0, by omega⟩ : Fin n) hi
        rw [shadowPerm_two n hn, hright]
        have ha : shadowActive n 2 (shadowShift n ⟨0, by omega⟩) := by
          exact (linear_shift_lower n 2 0 hn (by omega) (by omega) (by omega)).2
            (by omega)
        by_cases hfive : n = 5
        · subst hfive
          have hrightAct : shadowActive 5 2 (shadowShift 5 ⟨1, by omega⟩) := by
            rw [show shadowActive 5 2 (shadowShift 5 ⟨1, by omega⟩) ↔
                  (1 ≤ 2 ∧ 2 ≤ 5) by
                  simpa [shadowActive] using shadow_n4_active 5 2 (by omega) (by omega)]
            omega
          have hplast : (0 : Nat) ≠ 5 - 1 := by decide
          simpa [hplast] using (iff_of_true hrightAct ha)
        · have hrightAct : shadowActive n 2 (shadowShift n ⟨1, by omega⟩) := by
            exact (linear_shift_lower n 2 1 hn (by omega) (by omega) (by omega)).2
              (by omega)
          have hplast : (0 : Nat) ≠ n - 1 := Nat.ne_of_lt (by omega)
          simp [ha, hrightAct, hplast]
      · by_cases hmid : r ≤ n - 4
        · have h3 : 3 ≤ r := by omega
          have hright :
              right (⟨r - 2, by omega⟩ : Fin n) = ⟨r - 1, by omega⟩ := by
            have hi : (⟨r - 2, by omega⟩ : Fin n).val ≠ n - 1 := by
              simpa using (show r - 2 ≠ n - 1 by omega)
            have hval : (right (⟨r - 2, by omega⟩ : Fin n)).val = r - 2 + 1 := by
              simpa using right_val_eq_succ_of_val_ne_last
                (⟨r - 2, by omega⟩ : Fin n) hi
            apply Fin.ext
            calc
              (right (⟨r - 2, by omega⟩ : Fin n)).val = r - 2 + 1 := hval
              _ = r - 1 := by omega
          rw [shadowPerm_mid n hn r h3 (by omega), hright]
          have ha : shadowActive n r (shadowShift n ⟨r - 2, by omega⟩) := by
            exact (linear_shift_lower n r (r - 2) hn (by omega) (by omega) (by omega)).2
              (by omega)
          have hrightAct : shadowActive n r (shadowShift n ⟨r - 1, by omega⟩) := by
            exact (linear_shift_lower n r (r - 1) hn (by omega) (by omega) (by omega)).2
              (by omega)
          have hplast : (r - 2 : Nat) ≠ n - 1 := Nat.ne_of_lt (by omega)
          simp [ha, hrightAct, hplast]
        · by_cases hn3 : r = n - 3
          · subst hn3
            have hp :
                shadowPerm n hn ⟨n - 3, by omega⟩ = ⟨n - 5, by omega⟩ := by
              simpa using shadowPerm_mid n hn (n - 3) (by omega) (by omega)
            have hright :
                right (⟨n - 5, by omega⟩ : Fin n) = ⟨n - 4, by omega⟩ := by
              have hi : (⟨n - 5, by omega⟩ : Fin n).val ≠ n - 1 := by
                simpa using (show n - 5 ≠ n - 1 by omega)
              have hval : (right (⟨n - 5, by omega⟩ : Fin n)).val = n - 5 + 1 := by
                simpa using right_val_eq_succ_of_val_ne_last
                  (⟨n - 5, by omega⟩ : Fin n) hi
              apply Fin.ext
              calc
                (right (⟨n - 5, by omega⟩ : Fin n)).val = n - 5 + 1 := hval
                _ = n - 4 := by omega
            rw [hp, hright]
            have ha : shadowActive n (n - 3) (shadowShift n ⟨n - 5, by omega⟩) := by
              exact (linear_shift_lower n (n - 3) (n - 5) hn (by omega) (by omega) (by omega)).2
                (by omega)
            have hrightAct : shadowActive n (n - 3) (shadowShift n ⟨n - 4, by omega⟩) := by
              rw [show shadowActive n (n - 3) (shadowShift n ⟨n - 4, by omega⟩) ↔
                    (1 ≤ n - 3 ∧ n - 3 ≤ n) by
                    simpa [shadowActive] using shadow_n4_active n (n - 3) hn (by omega)]
              omega
            have hplast : (n - 5 : Nat) ≠ n - 1 := Nat.ne_of_lt (by omega)
            simp [ha, hrightAct, hplast]
          · by_cases hn2 : r = n - 2
            · subst hn2
              have hright :
                  right (⟨n - 2, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
                have hi : (⟨n - 2, by omega⟩ : Fin n).val ≠ n - 1 := by
                  simpa using (show n - 2 ≠ n - 1 by omega)
                have hval : (right (⟨n - 2, by omega⟩ : Fin n)).val = n - 2 + 1 := by
                  simpa using right_val_eq_succ_of_val_ne_last
                    (⟨n - 2, by omega⟩ : Fin n) hi
                apply Fin.ext
                calc
                  (right (⟨n - 2, by omega⟩ : Fin n)).val = n - 2 + 1 := hval
                  _ = n - 1 := by omega
              rw [shadowPerm_n_sub_two n hn, hright]
              have ha : shadowActive n (n - 2) (shadowShift n ⟨n - 2, by omega⟩) := by
                rw [show shadowActive n (n - 2) (shadowShift n ⟨n - 2, by omega⟩) ↔
                      (n - 2 ≤ n - 2 ∨ n - 2 = 2 * n - 1) by
                      simpa [shadowActive] using shadow_n2_active n (n - 2) hn (by omega)]
                exact Or.inl (by omega)
              have hrightAct : shadowActive n (n - 2) (shadowShift n ⟨n - 1, by omega⟩) := by
                rw [show shadowActive n (n - 2) (shadowShift n ⟨n - 1, by omega⟩) ↔
                      (2 ≤ n - 2 ∧ n - 2 ≤ n + 1) by
                      simpa [shadowActive] using shadow_n1_active n (n - 2) hn (by omega)]
                omega
              have hplast : (n - 2 : Nat) ≠ n - 1 := Nat.ne_of_lt (by omega)
              simp [ha, hrightAct, hplast]
            · have hlast : r = n - 1 := by omega
              subst hlast
              have hright :
                  right (⟨n - 3, by omega⟩ : Fin n) = ⟨n - 2, by omega⟩ := by
                have hi : (⟨n - 3, by omega⟩ : Fin n).val ≠ n - 1 := by
                  simpa using (show n - 3 ≠ n - 1 by omega)
                have hval : (right (⟨n - 3, by omega⟩ : Fin n)).val = n - 3 + 1 := by
                  simpa using right_val_eq_succ_of_val_ne_last
                    (⟨n - 3, by omega⟩ : Fin n) hi
                apply Fin.ext
                calc
                  (right (⟨n - 3, by omega⟩ : Fin n)).val = n - 3 + 1 := hval
                  _ = n - 2 := by omega
              rw [shadowPerm_n_sub_one n hn, hright]
              have ha : ¬ shadowActive n (n - 1) (shadowShift n ⟨n - 3, by omega⟩) := by
                rw [show shadowActive n (n - 1) (shadowShift n ⟨n - 3, by omega⟩) ↔
                      n ≤ n - 1 by
                      simpa [shadowActive] using shadow_n3_active n (n - 1) hn (by omega)]
                omega
              have hrightAct : ¬ shadowActive n (n - 1) (shadowShift n ⟨n - 2, by omega⟩) := by
                rw [show shadowActive n (n - 1) (shadowShift n ⟨n - 2, by omega⟩) ↔
                      (n - 1 ≤ n - 2 ∨ n - 1 = 2 * n - 1) by
                      simpa [shadowActive] using shadow_n2_active n (n - 1) hn (by omega)]
                omega
              have hplast : (n - 3 : Nat) ≠ n - 1 := Nat.ne_of_lt (by omega)
              simp [ha, hrightAct, hplast]

private lemma shadow_right_active
    (n : Nat) (hn : 5 ≤ n) (k : Fin (2 * n)) :
    let p : Fin n := shadowPerm n hn ⟨k.val % n, Nat.mod_lt _ (by omega)⟩
    let a := shadowActive n k.val (shadowShift n p)
    shadowActive n k.val (shadowShift n (right p)) ↔ (a ↔ p.val ≠ n - 1) := by
  let r : Nat := k.val % n
  let p : Fin n := shadowPerm n hn ⟨r, Nat.mod_lt _ (by omega)⟩
  have hr : r < n := by
    dsimp [r]
    exact Nat.mod_lt _ (by omega)
  rcases mod_two_period_boundary_local n k.val (by omega) k.isLt with ⟨_, hk_eq⟩ | ⟨_, hk_eq⟩
  · have hk_eq' : k.val = r := by
      simpa [r] using hk_eq
    rw [hk_eq']
    simpa [r, p] using shadow_right_first_half_active n hn r hr
  · have hk_eq' : k.val = r + n := by
      simpa [r] using hk_eq
    rw [hk_eq']
    have hrmod : (r + n) % n = r := mod_add_period_local n r (by omega) hr
    have hrself : r % n = r := Nat.mod_eq_of_lt hr
    have hp :
        shadowPerm n hn ⟨(r + n) % n, Nat.mod_lt _ (by omega)⟩ = p := by
      apply Fin.ext
      simpa [p, hrmod]
    have hbase :
        shadowActive n r (shadowShift n (right p)) ↔
          (shadowActive n r (shadowShift n p) ↔ p.val ≠ n - 1) := by
      simpa [r, p] using shadow_right_first_half_active n hn r hr
    have hRflip :
        shadowActive n (r + n) (shadowShift n (right p)) ↔
          ¬ shadowActive n r (shadowShift n (right p)) :=
      shadowActive_add_n_iff_not n r (shadowShift n (right p)) (by omega)
    have hAflip :
        shadowActive n (r + n) (shadowShift n p) ↔
          ¬ shadowActive n r (shadowShift n p) :=
      shadowActive_add_n_iff_not n r (shadowShift n p) (by omega)
    by_cases hplast : p.val = n - 1
    · have hbase' :
          shadowActive n r (shadowShift n (right p)) ↔
            ¬ shadowActive n r (shadowShift n p) := by
        simpa [hplast] using hbase
      have hgoal :
          shadowActive n (r + n) (shadowShift n (right p)) ↔
            ¬ shadowActive n (r + n) (shadowShift n p) := by
        calc
          shadowActive n (r + n) (shadowShift n (right p))
              ↔ ¬ shadowActive n r (shadowShift n (right p)) := hRflip
          _ ↔ ¬¬ shadowActive n r (shadowShift n p) := by simpa [hbase']
          _ ↔ ¬ shadowActive n (r + n) (shadowShift n p) := by
                simpa using (not_congr hAflip).symm
      simpa [hplast, p, hp, hrself] using hgoal
    · have hbase' :
          shadowActive n r (shadowShift n (right p)) ↔
            shadowActive n r (shadowShift n p) := by
        simpa [hplast] using hbase
      have hgoal :
          shadowActive n (r + n) (shadowShift n (right p)) ↔
            shadowActive n (r + n) (shadowShift n p) := by
        calc
          shadowActive n (r + n) (shadowShift n (right p))
              ↔ ¬ shadowActive n r (shadowShift n (right p)) := hRflip
          _ ↔ ¬ shadowActive n r (shadowShift n p) := by simpa [hbase']
          _ ↔ shadowActive n (r + n) (shadowShift n p) := hAflip.symm
      simpa [hplast, p, hp, hrself] using hgoal

private lemma shadow_center_next_active
    (n : Nat) (hn : 5 ≤ n) (k : Fin (2 * n)) :
    let p : Fin n := shadowPerm n hn ⟨k.val % n, Nat.mod_lt _ (by omega)⟩
    shadowActive n ((k.val + 1) % (2 * n)) (shadowShift n p) ↔
      ¬ shadowActive n k.val (shadowShift n p) := by
  dsimp
  let p : Fin n := shadowPerm n hn ⟨k.val % n, Nat.mod_lt _ (by omega)⟩
  let r : Nat := (k.val + shadowShift n p) % (2 * n)
  have hr_boundary : r = 0 ∨ r = n := by
    simpa [r] using shadow_boundary_at_perm n hn k.val k.isLt
  have hshift :
      ((k.val + 1) % (2 * n) + shadowShift n p) % (2 * n) = (r + 1) % (2 * n) := by
    simpa [r] using mod_shift_eq n k.val (shadowShift n p) (by omega)
  rcases hr_boundary with hr0 | hrn
  · have hcurr_false : ¬ shadowActive n k.val (shadowShift n p) := by
      intro h
      have hpair :
          1 ≤ (k.val + shadowShift n p) % (2 * n) ∧
            (k.val + shadowShift n p) % (2 * n) ≤ n := by
        simpa [shadowActive] using h
      have : 1 ≤ 0 := by
        simpa [r, hr0] using hpair.1
      omega
    have hnext_res :
        ((k.val + 1) % (2 * n) + shadowShift n p) % (2 * n) = 1 := by
      rw [hshift, hr0]
      simpa using (Nat.mod_eq_of_lt (show 1 < 2 * n by omega))
    have hnext_true : shadowActive n ((k.val + 1) % (2 * n)) (shadowShift n p) := by
      have hcond : 1 ≤ 1 ∧ 1 ≤ n := by omega
      simpa [shadowActive, hnext_res] using hcond
    exact iff_of_true hnext_true hcurr_false
  · have hcurr_true : shadowActive n k.val (shadowShift n p) := by
      have hcond : 1 ≤ n ∧ n ≤ n := by omega
      have hpair :
          1 ≤ (k.val + shadowShift n p) % (2 * n) ∧
            (k.val + shadowShift n p) % (2 * n) ≤ n := by
        simpa [r, hrn] using hcond
      simpa [shadowActive] using hpair
    have hnext_res :
        ((k.val + 1) % (2 * n) + shadowShift n p) % (2 * n) = n + 1 := by
      rw [hshift, hrn]
      simpa using (Nat.mod_eq_of_lt (show n + 1 < 2 * n by omega))
    have hnext_false : ¬ shadowActive n ((k.val + 1) % (2 * n)) (shadowShift n p) := by
      intro h
      have hcond : 1 ≤ n + 1 ∧ n + 1 ≤ n := by
        simpa [shadowActive, hnext_res] using h
      omega
    exact iff_of_false hnext_false (by intro hneg; exact hneg hcurr_true)

private lemma shadowMatchIndex_next_center_waterfall_active
    (wc : WaterfallCycle sys) (hn : 5 ≤ sys.rs.n) (k : Fin (2 * sys.rs.n)) :
    let p : Fin sys.rs.n :=
      shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
    let a := shadowActive sys.rs.n k.val (shadowShift sys.rs.n p)
    let j := shadowMatchIndex wc hn k
    (1 ≤ ((nextIndex wc.configs j).val + 2 * sys.rs.n - p.val) % (2 * sys.rs.n) ∧
        ((nextIndex wc.configs j).val + 2 * sys.rs.n - p.val) % (2 * sys.rs.n) ≤ sys.rs.n) ↔
      ¬ a := by
  dsimp
  let p : Fin sys.rs.n :=
    shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
  let a : Prop := shadowActive sys.rs.n k.val (shadowShift sys.rs.n p)
  let j := shadowMatchIndex wc hn k
  let jnext := nextIndex wc.configs j
  have hw :=
    waterfall_active_iff sys.rs.n jnext.val p.val hn
      (by simpa [jnext, wc.len_eq] using jnext.isLt)
      p.isLt
  rw [hw]
  by_cases hact : a
  · have hj0 : j.val = p.val + (if a then sys.rs.n else 0) := by
        simp [j, shadowMatchIndex, p, a]
    have hj : j.val = p.val + sys.rs.n := by
      simpa [hact] using hj0
    by_cases hplast : p.val = sys.rs.n - 1
    · have hnext : jnext.val = 0 := by
        calc
          jnext.val = (j.val + 1) % wc.configs.length := rfl
          _ = (p.val + sys.rs.n + 1) % (2 * sys.rs.n) := by
                rw [hj, wc.len_eq]
          _ = 0 := by
                rw [hplast]
                have : sys.rs.n - 1 + sys.rs.n + 1 = 2 * sys.rs.n := by omega
                rw [this, Nat.mod_self]
      have hfalse : ¬ (p.val + 1 ≤ jnext.val ∧ jnext.val ≤ p.val + sys.rs.n) := by
        rw [hnext]
        omega
      constructor
      · intro hinterval
        exact False.elim (hfalse hinterval)
      · intro hneg
        exact False.elim (hneg hact)
    · have hnext : jnext.val = p.val + sys.rs.n + 1 := by
        calc
          jnext.val = (j.val + 1) % wc.configs.length := rfl
          _ = (p.val + sys.rs.n + 1) % (2 * sys.rs.n) := by
                rw [hj, wc.len_eq]
          _ = p.val + sys.rs.n + 1 := by
                exact Nat.mod_eq_of_lt (by
                  have hp : p.val < sys.rs.n := p.isLt
                  omega)
      have hfalse : ¬ (p.val + 1 ≤ jnext.val ∧ jnext.val ≤ p.val + sys.rs.n) := by
        rw [hnext]
        omega
      constructor
      · intro hinterval
        exact False.elim (hfalse hinterval)
      · intro hneg
        exact False.elim (hneg hact)
  · have hj0 : j.val = p.val + (if a then sys.rs.n else 0) := by
        simp [j, shadowMatchIndex, p, a]
    have hj : j.val = p.val := by
      simpa [hact] using hj0
    have hnext : jnext.val = p.val + 1 := by
      calc
        jnext.val = (j.val + 1) % wc.configs.length := rfl
        _ = (p.val + 1) % (2 * sys.rs.n) := by
              rw [hj, wc.len_eq]
        _ = p.val + 1 := by
              exact Nat.mod_eq_of_lt (by
                have hp : p.val < sys.rs.n := p.isLt
                omega)
    have htrue : p.val + 1 ≤ jnext.val ∧ jnext.val ≤ p.val + sys.rs.n := by
      rw [hnext]
      omega
    constructor
    · intro _
      simpa [a] using hact
    · intro _
      exact htrue

private lemma waterfall_eq_ite
    (wc : WaterfallCycle sys) (j : Fin wc.configs.length) (q : Fin sys.rs.n) :
    (wc.configs.get j) q =
      (if 1 ≤ (j.val + 2 * sys.rs.n - q.val) % (2 * sys.rs.n) ∧
            (j.val + 2 * sys.rs.n - q.val) % (2 * sys.rs.n) ≤ sys.rs.n
       then wc.highVal q
       else ⟨0, by have := sys.rs.m_pos q; omega⟩) := by
  have hw := wc.waterfall j q
  dsimp only at hw
  by_cases h :
      1 ≤ (j.val + 2 * sys.rs.n - q.val) % (2 * sys.rs.n) ∧
        (j.val + 2 * sys.rs.n - q.val) % (2 * sys.rs.n) ≤ sys.rs.n
  · simpa [h] using hw
  · simpa [h] using hw

private lemma shadowMatchIndex_left_eq
    (wc : WaterfallCycle sys) (hn : 5 ≤ sys.rs.n) (k : Fin (2 * sys.rs.n)) :
    let p : Fin sys.rs.n :=
      shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
    canonicalShadowConfig wc k (left p) =
      (wc.configs.get (shadowMatchIndex wc hn k)) (left p) := by
  dsimp
  let p : Fin sys.rs.n :=
    shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
  let j := shadowMatchIndex wc hn k
  let wactive : Prop :=
    1 ≤ (j.val + 2 * sys.rs.n - (left p).val) % (2 * sys.rs.n) ∧
      (j.val + 2 * sys.rs.n - (left p).val) % (2 * sys.rs.n) ≤ sys.rs.n
  have hshadow :
      shadowActive sys.rs.n k.val (shadowShift sys.rs.n (left p)) ↔
        (shadowActive sys.rs.n k.val (shadowShift sys.rs.n p) ↔ p.val = 0) := by
    simpa [p] using shadow_left_active sys.rs.n hn k
  have hwater :
      wactive ↔
        (shadowActive sys.rs.n k.val (shadowShift sys.rs.n p) ↔ p.val = 0) := by
    simpa [p, j, wactive] using shadowMatchIndex_left_waterfall_active wc hn k
  have hiff :
      shadowActive sys.rs.n k.val (shadowShift sys.rs.n (left p)) ↔ wactive := by
    exact hshadow.trans hwater.symm
  have hite :=
    shadow_val_eq_ite (sys.rs.m_pos (left p)) (wc.highVal (left p))
      (wc.highVal_pos (left p))
      (shadowActive sys.rs.n k.val (shadowShift sys.rs.n (left p)))
      wactive hiff
  calc
    canonicalShadowConfig wc k (left p)
        = (if shadowActive sys.rs.n k.val (shadowShift sys.rs.n (left p))
            then wc.highVal (left p)
            else ⟨0, by have := sys.rs.m_pos (left p); omega⟩) := by
              simp [canonicalShadowConfig, p]
    _ = (if wactive
          then wc.highVal (left p)
          else ⟨0, by have := sys.rs.m_pos (left p); omega⟩) := hite
    _ = (wc.configs.get j) (left p) := by
          symm
          simpa [p, j, wactive] using waterfall_eq_ite wc j (left p)

private lemma shadowMatchIndex_right_eq
    (wc : WaterfallCycle sys) (hn : 5 ≤ sys.rs.n) (k : Fin (2 * sys.rs.n)) :
    let p : Fin sys.rs.n :=
      shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
    canonicalShadowConfig wc k (right p) =
      (wc.configs.get (shadowMatchIndex wc hn k)) (right p) := by
  dsimp
  let p : Fin sys.rs.n :=
    shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
  let j := shadowMatchIndex wc hn k
  let wactive : Prop :=
    1 ≤ (j.val + 2 * sys.rs.n - (right p).val) % (2 * sys.rs.n) ∧
      (j.val + 2 * sys.rs.n - (right p).val) % (2 * sys.rs.n) ≤ sys.rs.n
  have hshadow :
      shadowActive sys.rs.n k.val (shadowShift sys.rs.n (right p)) ↔
        (shadowActive sys.rs.n k.val (shadowShift sys.rs.n p) ↔ p.val ≠ sys.rs.n - 1) := by
    simpa [p] using shadow_right_active sys.rs.n hn k
  have hwater :
      wactive ↔
        (shadowActive sys.rs.n k.val (shadowShift sys.rs.n p) ↔ p.val ≠ sys.rs.n - 1) := by
    simpa [p, j, wactive] using shadowMatchIndex_right_waterfall_active wc hn k
  have hiff :
      shadowActive sys.rs.n k.val (shadowShift sys.rs.n (right p)) ↔ wactive := by
    exact hshadow.trans hwater.symm
  have hite :=
    shadow_val_eq_ite (sys.rs.m_pos (right p)) (wc.highVal (right p))
      (wc.highVal_pos (right p))
      (shadowActive sys.rs.n k.val (shadowShift sys.rs.n (right p)))
      wactive hiff
  calc
    canonicalShadowConfig wc k (right p)
        = (if shadowActive sys.rs.n k.val (shadowShift sys.rs.n (right p))
            then wc.highVal (right p)
            else ⟨0, by have := sys.rs.m_pos (right p); omega⟩) := by
              simp [canonicalShadowConfig, p]
    _ = (if wactive
          then wc.highVal (right p)
          else ⟨0, by have := sys.rs.m_pos (right p); omega⟩) := hite
    _ = (wc.configs.get j) (right p) := by
          symm
          simpa [p, j, wactive] using waterfall_eq_ite wc j (right p)

private lemma shadowMatchIndex_next_center_eq
    (wc : WaterfallCycle sys) (hn : 5 ≤ sys.rs.n) (k : Fin (2 * sys.rs.n)) :
    let p : Fin sys.rs.n :=
      shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
    canonicalShadowConfig wc
        ⟨(k.val + 1) % (2 * sys.rs.n), Nat.mod_lt _ (by omega)⟩ p =
      (wc.configs.get (nextIndex wc.configs (shadowMatchIndex wc hn k))) p := by
  dsimp
  let p : Fin sys.rs.n :=
    shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
  let j := shadowMatchIndex wc hn k
  let wactive : Prop :=
    1 ≤ ((nextIndex wc.configs j).val + 2 * sys.rs.n - p.val) % (2 * sys.rs.n) ∧
      ((nextIndex wc.configs j).val + 2 * sys.rs.n - p.val) % (2 * sys.rs.n) ≤ sys.rs.n
  have hshadow :
      shadowActive sys.rs.n ((k.val + 1) % (2 * sys.rs.n))
          (shadowShift sys.rs.n p) ↔
        ¬ shadowActive sys.rs.n k.val (shadowShift sys.rs.n p) := by
    simpa [p] using shadow_center_next_active sys.rs.n hn k
  have hwater :
      wactive ↔ ¬ shadowActive sys.rs.n k.val (shadowShift sys.rs.n p) := by
    simpa [p, j, wactive] using shadowMatchIndex_next_center_waterfall_active wc hn k
  have hiff :
      shadowActive sys.rs.n ((k.val + 1) % (2 * sys.rs.n))
          (shadowShift sys.rs.n p) ↔
        wactive := by
    exact hshadow.trans hwater.symm
  have hite :=
    shadow_val_eq_ite (sys.rs.m_pos p) (wc.highVal p) (wc.highVal_pos p)
      (shadowActive sys.rs.n ((k.val + 1) % (2 * sys.rs.n))
        (shadowShift sys.rs.n p))
      wactive hiff
  calc
    canonicalShadowConfig wc
        ⟨(k.val + 1) % (2 * sys.rs.n), Nat.mod_lt _ (by omega)⟩ p
        = (if shadowActive sys.rs.n ((k.val + 1) % (2 * sys.rs.n))
              (shadowShift sys.rs.n p)
            then wc.highVal p
            else ⟨0, by have := sys.rs.m_pos p; omega⟩) := by
              simp [canonicalShadowConfig, p]
    _ = (if wactive
          then wc.highVal p
          else ⟨0, by have := sys.rs.m_pos p; omega⟩) := hite
    _ = (wc.configs.get (nextIndex wc.configs j)) p := by
          symm
          simpa [p, j, wactive] using waterfall_eq_ite wc (nextIndex wc.configs j) p

private lemma shadowMatchIndex_center_eq
    (wc : WaterfallCycle sys) (hn : 5 ≤ sys.rs.n) (k : Fin (2 * sys.rs.n)) :
    let p : Fin sys.rs.n :=
      shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
    canonicalShadowConfig wc k p = (wc.configs.get (shadowMatchIndex wc hn k)) p := by
  dsimp
  let p : Fin sys.rs.n :=
    shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
  let j := shadowMatchIndex wc hn k
  have hboundary := shadow_boundary_at_perm sys.rs.n hn k.val k.isLt
  have hw := wc.waterfall j p
  dsimp only at hw
  by_cases hact : shadowActive sys.rs.n k.val (shadowShift sys.rs.n p)
  · have hkshift :
        (k.val + shadowShift sys.rs.n p) % (2 * sys.rs.n) = sys.rs.n := by
      rcases hboundary with h0 | hn0
      · exfalso
        have hzero : (k.val + shadowShift sys.rs.n p) % (2 * sys.rs.n) = 0 := by
          simpa [p] using h0
        have : 1 ≤ 0 := by
          simpa [shadowActive, hzero] using hact.1
        omega
      · exact hn0
    have hcond :
        1 ≤ (j.val + 2 * sys.rs.n - p.val) % (2 * sys.rs.n) ∧
          (j.val + 2 * sys.rs.n - p.val) % (2 * sys.rs.n) ≤ sys.rs.n := by
      have hsum : j.val + 2 * sys.rs.n - p.val = sys.rs.n + 2 * sys.rs.n := by
        have hp : p.val < sys.rs.n := p.isLt
        simp [j, p, shadowMatchIndex, hact]
        omega
      rw [hsum,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    have hact' :
        1 ≤ (k.val + shadowShift sys.rs.n p) % (2 * sys.rs.n) ∧
          (k.val + shadowShift sys.rs.n p) % (2 * sys.rs.n) ≤ sys.rs.n := by
      simpa [shadowActive] using hact
    have hw' : (wc.configs.get j) p = wc.highVal p := by
      simpa [hcond] using hw
    simpa [canonicalShadowConfig, shadowActive, hact', p] using hw'.symm
  · have hkshift :
        (k.val + shadowShift sys.rs.n p) % (2 * sys.rs.n) = 0 := by
      rcases hboundary with h0 | hn0
      · simpa [p] using h0
      · exfalso
        have hact' :
            1 ≤ (k.val + shadowShift sys.rs.n p) % (2 * sys.rs.n) ∧
              (k.val + shadowShift sys.rs.n p) % (2 * sys.rs.n) ≤ sys.rs.n := by
          rw [hn0]
          omega
        exact hact (by simpa [shadowActive] using hact')
    have hcond :
        ¬(1 ≤ (j.val + 2 * sys.rs.n - p.val) % (2 * sys.rs.n) ∧
            (j.val + 2 * sys.rs.n - p.val) % (2 * sys.rs.n) ≤ sys.rs.n) := by
      rw [show j.val + 2 * sys.rs.n - p.val = 2 * sys.rs.n by
            simp [j, p, shadowMatchIndex, hact],
        Nat.mod_self]
      omega
    have hact' :
        ¬(1 ≤ (k.val + shadowShift sys.rs.n p) % (2 * sys.rs.n) ∧
            (k.val + shadowShift sys.rs.n p) % (2 * sys.rs.n) ≤ sys.rs.n) := by
      simpa [shadowActive] using hact
    have hw' : (wc.configs.get j) p = ⟨0, by have := sys.rs.m_pos p; omega⟩ := by
      simpa [hcond] using hw
    simpa [canonicalShadowConfig, shadowActive, hact', p] using hw'.symm

private theorem shadow_entryCore_of_local_context
    (wc : WaterfallCycle sys) (hn : 5 ≤ sys.rs.n) (k : Fin (2 * sys.rs.n)) :
    let p : Fin sys.rs.n :=
      shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
    let j := shadowMatchIndex wc hn k
    canonicalShadowConfig wc k (left p) = (wc.configs.get j) (left p) →
    canonicalShadowConfig wc k p = (wc.configs.get j) p →
    canonicalShadowConfig wc k (right p) = (wc.configs.get j) (right p) →
    canonicalShadowConfig wc
        ⟨(k.val + 1) % (2 * sys.rs.n), Nat.mod_lt _ (by omega)⟩ p =
      (wc.configs.get (nextIndex wc.configs j)) p →
    privileged sys (canonicalShadowConfig wc k) p ∧
      canonicalShadowConfig wc
        ⟨(k.val + 1) % (2 * sys.rs.n), Nat.mod_lt _ (by omega)⟩ p =
          move sys (canonicalShadowConfig wc k) p p := by
  dsimp
  let p : Fin sys.rs.n :=
    shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
  let j := shadowMatchIndex wc hn k
  intro hL hS hR hnext
  have hL' : canonicalShadowConfig wc k (left p) = (wc.configs.get j) (left p) := by
    simpa [p, j] using hL
  have hS' : canonicalShadowConfig wc k p = (wc.configs.get j) p := by
    simpa [p, j] using hS
  have hR' : canonicalShadowConfig wc k (right p) = (wc.configs.get j) (right p) := by
    simpa [p, j] using hR
  have hnext' :
      canonicalShadowConfig wc
          ⟨(k.val + 1) % (2 * sys.rs.n), Nat.mod_lt _ (by omega)⟩ p =
        (wc.configs.get (nextIndex wc.configs j)) p := by
    simpa [p, j] using hnext
  have hmover : wc.toGoodCycle.moverAt j = p := by
    simpa [j, p] using shadowMatchIndex_moverAt wc hn k
  have hprivW : privileged sys (wc.configs.get j) p := by
    rw [← hmover]
    exact wc.toGoodCycle.moverAt_privileged j
  have hprivS : privileged sys (canonicalShadowConfig wc k) p := by
    unfold privileged
    rw [hL', hS', hR']
    simpa [privileged] using hprivW
  constructor
  · exact hprivS
  · have hstep :=
      wc.toGoodCycle.step_eq_move j
    have hmoveP :
        (wc.configs.get (nextIndex wc.configs j)) p =
          move sys (wc.configs.get j) p p := by
      simpa [hmover] using congrFun hstep p
    calc
      canonicalShadowConfig wc
          ⟨(k.val + 1) % (2 * sys.rs.n), Nat.mod_lt _ (by omega)⟩ p
          = (wc.configs.get (nextIndex wc.configs j)) p := hnext'
      _ = move sys (wc.configs.get j) p p := hmoveP
      _ = move sys (canonicalShadowConfig wc k) p p := by
        unfold move
        simp
        change
          sys.f p (wc.configs.get j (left p)) (wc.configs.get j p)
              (wc.configs.get j (right p)) =
            sys.f p (canonicalShadowConfig wc k (left p))
              (canonicalShadowConfig wc k p)
              (canonicalShadowConfig wc k (right p))
        rw [hL', hS', hR']

theorem canonicalShadow_entry_of_local_context
    (wc : WaterfallCycle sys) (hn : 5 ≤ sys.rs.n) :
    ∀ k : Fin (2 * sys.rs.n),
      let p : Fin sys.rs.n :=
        shadowPerm sys.rs.n hn ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
      privileged sys (canonicalShadowConfig wc k) p ∧
        canonicalShadowConfig wc
          ⟨(k.val + 1) % (2 * sys.rs.n), Nat.mod_lt _ (by omega)⟩ p =
            move sys (canonicalShadowConfig wc k) p p := by
  intro k
  exact shadow_entryCore_of_local_context wc hn k
    (by simpa using shadowMatchIndex_left_eq wc hn k)
    (by simpa using shadowMatchIndex_center_eq wc hn k)
    (by simpa using shadowMatchIndex_right_eq wc hn k)
    (by simpa using shadowMatchIndex_next_center_eq wc hn k)

/-! ### Shadow trap assembly -/

-- Convert the shadow construction into a ShadowTrap structure.
-- This bridges the gap between the shadow formula and the
-- well-foundedness obstruction from MNU.lean.
theorem shadow_gives_trap (wc : WaterfallCycle sys)
    (sc : ShadowConstruction wc)
    (_hclosure : shadowClosure sc)
    (_hdistinct : shadowDistinct sc)
    (_hdisjoint : shadowDisjoint sc) :
    ∃ st : ShadowTrap sys wc.toGoodCycle, True := by
  refine ⟨⟨List.ofFn sc.configs, ?_, ?_, ?_, ?_⟩, trivial⟩
  -- nonempty
  · simp; have := shadow_len_pos sc; omega
  -- disjoint
  · rw [List.forall_mem_ofFn_iff]; exact _hdisjoint
  -- closed
  · intro k
    have hlen : (List.ofFn sc.configs).length = sc.len := List.length_ofFn
    have hk' : k.val < sc.len := by have := k.isLt; have := hlen; omega
    obtain ⟨p, hp, hstep⟩ := _hclosure ⟨k.val, hk'⟩
    refine ⟨p, ?_, ?_⟩
    · simp only [List.get_ofFn]; convert hp using 2
    · simp only [List.get_ofFn, nextIndex]
      convert hstep using 2 <;> simp [hlen]
  -- distinct
  · rw [List.nodup_ofFn]
    exact fun _ _ h => _hdistinct _ _ h

/-! ### The Shadow Cycle Mirror Theorem -/

-- Shadow Cycle Mirror Theorem (Claim 4.4.1).
-- For n >= 5 with >= 3 binary processors, any uniform sweep good cycle
-- cannot be part of a self-stabilizing system.
-- Proof: construct the shadow trap, then apply shadowTrap_not_converges.
theorem shadow_cycle_mirror_theorem
    (wc : WaterfallCycle sys)
    (hn : sys.rs.n ≥ 5)
    (_h3bin : hasGe3Binary sys.rs) :
    ¬converges sys wc.toGoodCycle := by
  let sc := canonicalShadowConstruction wc
  have hentry := canonicalShadow_entry_of_local_context wc (by omega)
  have hclosure : shadowClosure sc := by
    simpa [sc] using canonicalShadowClosure_of_entryCore wc (by omega) hentry
  have hdistinct : shadowDistinct sc := by
    simpa [sc] using canonicalShadowDistinct wc (by omega)
  have hdisjoint : shadowDisjoint sc := by
    simpa [sc] using canonicalShadowDisjoint wc (by omega)
  rcases shadow_gives_trap wc sc hclosure hdistinct hdisjoint with ⟨st, _⟩
  exact shadowTrap_not_converges wc.toGoodCycle st

-- Corollary: no valid system with a waterfall cycle exists when n >= 5
-- and there are >= 3 binary processors.
theorem no_valid_sweep_system
    (wc : WaterfallCycle sys)
    (hn : sys.rs.n ≥ 5)
    (h3bin : hasGe3Binary sys.rs)
    (hconv : converges sys wc.toGoodCycle) :
    False :=
  shadow_cycle_mirror_theorem wc hn h3bin hconv

end LeanMn
