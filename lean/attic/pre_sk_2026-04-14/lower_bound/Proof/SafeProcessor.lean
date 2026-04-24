/-
  SafeProcessor.lean — Safe processor and all-stay shadow traps

  Case A: Some processor q is at distance ≥ 2 from every mover at every step.
  Case B: Zero winding with cw = 0 (all steps are stay).

  Both derive contradiction by flipping a far processor's value → shadow cycle
  of non-good configs → badStep cycle → ¬converges.

  Sorry-free. Ported from ZeroWindingAssembly.lean.
-/
import LeanMn.LowerBound.CycleTypes

namespace LeanMn

variable {sys : System}

/-! ### Helpers -/

private noncomputable def flipConfig (c : Config sys.rs) (q : Fin sys.rs.n)
    (v : Fin (sys.rs.m q)) : Config sys.rs :=
  fun j => if h : j = q then h ▸ v else c j

private theorem flipConfig_eq_of_ne (c : Config sys.rs) (q : Fin sys.rs.n)
    (v : Fin (sys.rs.m q)) (j : Fin sys.rs.n) (hj : j ≠ q) :
    flipConfig c q v j = c j := by
  simp [flipConfig, hj]

private theorem flipConfig_at_q (c : Config sys.rs) (q : Fin sys.rs.n)
    (v : Fin (sys.rs.m q)) :
    flipConfig c q v q = v := by
  simp [flipConfig]

private theorem move_ne_eq (c : Config sys.rs) (p q : Fin sys.rs.n) (hq : q ≠ p) :
    (move sys c p) q = c q := by
  simp [move, hq]

private theorem exists_ne_val (q : Fin sys.rs.n) (v : Fin (sys.rs.m q)) :
    ∃ v' : Fin (sys.rs.m q), v' ≠ v := by
  have hm : 2 ≤ sys.rs.m q := sys.rs.m_pos q
  have hvlt := v.isLt
  have hlt : (v.val + 1) % sys.rs.m q < sys.rs.m q := Nat.mod_lt _ (by omega)
  refine ⟨⟨(v.val + 1) % sys.rs.m q, hlt⟩, ?_⟩
  intro h
  have hval : (v.val + 1) % sys.rs.m q = v.val := congrArg Fin.val h
  have : (v.val + 1) % sys.rs.m q ≠ v.val := by
    by_cases hvmax : v.val + 1 < sys.rs.m q
    · rw [Nat.mod_eq_of_lt hvmax]; omega
    · rw [show v.val + 1 = sys.rs.m q from by omega, Nat.mod_self]; omega
  exact this hval

private theorem privileged_of_same_context (gc : GoodCycle sys)
    (k : Fin gc.configs.length) (c : Config sys.rs)
    (p : Fin sys.rs.n) (hmov : gc.moverAt k = p)
    (hL : c (left p) = (gc.configs.get k) (left p))
    (hS : c p = (gc.configs.get k) p)
    (hR : c (right p) = (gc.configs.get k) (right p)) :
    privileged sys c p := by
  unfold privileged
  rw [hL, hS, hR, ← hmov]
  exact gc.moverAt_privileged k

private theorem not_acc_of_finite_cycle {α : Type*} {r : α → α → Prop}
    {n : Nat} (hn : 0 < n) (f : Fin n → α)
    (hcycle : ∀ k : Fin n, r (f ⟨(k.val + 1) % n, Nat.mod_lt _ hn⟩) (f k)) :
    ∀ k : Fin n, ¬Acc r (f k) := by
  suffices h : ∀ x, Acc r x → (∀ k : Fin n, f k ≠ x) from
    fun k hacc => h (f k) hacc k rfl
  intro x hacc
  induction hacc with
  | intro x _ ih =>
    intro k hfk
    subst hfk
    exact ih _ (hcycle k) ⟨(k.val + 1) % n, Nat.mod_lt _ hn⟩ rfl

/-! ### Helper: n ≥ 5 → every processor has a far processor -/

private theorem exists_far_processor (hn : sys.rs.n ≥ 5) (p : Fin sys.rs.n) :
    ∃ q : Fin sys.rs.n, q ≠ p ∧ q ≠ left p ∧ q ≠ right p ∧
      left q ≠ p ∧ right q ≠ p := by
  obtain ⟨q, hq_ne_p, hq_ne_lp, hq_ne_rp⟩ :
      ∃ q : Fin sys.rs.n, q ≠ p ∧ q ≠ left p ∧ q ≠ right p := by
    by_contra hall
    push_neg at hall
    have htri : ∀ x : Fin sys.rs.n, x = p ∨ x = left p ∨ x = right p := by
      intro x; by_contra hx; push_neg at hx
      exact hx.2.2 (hall x hx.1 hx.2.1)
    have hsub : (Finset.univ : Finset (Fin sys.rs.n)) ⊆ {p, left p, right p} := by
      intro x _; simp only [Finset.mem_insert, Finset.mem_singleton]; exact htri x
    have hle := Finset.card_le_card hsub
    rw [Finset.card_fin] at hle
    have h3 : ({p, left p, right p} : Finset (Fin sys.rs.n)).card ≤ 3 := by
      have : ({p, left p, right p} : Finset (Fin sys.rs.n)) ⊆
          ({p} : Finset _) ∪ ({left p} : Finset _) ∪ ({right p} : Finset _) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_union, Finset.mem_singleton]
        rcases hx with rfl | rfl | rfl
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr rfl
      calc ({p, left p, right p} : Finset _).card
          ≤ (({p} : Finset _) ∪ ({left p} : Finset _) ∪ ({right p} : Finset _)).card :=
            Finset.card_le_card this
        _ ≤ (({p} : Finset _) ∪ ({left p} : Finset _)).card +
              ({right p} : Finset _).card :=
            Finset.card_union_le _ _
        _ ≤ ({p} : Finset _).card + ({left p} : Finset _).card +
              ({right p} : Finset _).card := by
            linarith [Finset.card_union_le ({p} : Finset _) ({left p} : Finset _)]
        _ = 3 := by simp
    omega
  refine ⟨q, hq_ne_p, hq_ne_lp, hq_ne_rp, ?_, ?_⟩
  · intro hlq
    exact hq_ne_rp (by
      calc q = right (left q) := by simp [right_left_eq_self]
        _ = right p := by rw [hlq])
  · intro hrq
    exact hq_ne_lp (by
      calc q = left (right q) := by simp [left_right_eq_self]
        _ = left p := by rw [hrq])

/-! ### Config value constant for non-movers -/

private theorem config_val_const_at_neverMover (gc : GoodCycle sys)
    (q : Fin sys.rs.n)
    (hq_never : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ q)
    (k : Fin gc.configs.length) :
    (gc.configs.get k) q = (gc.configs.get ⟨0, gc.configs_length_pos⟩) q := by
  obtain ⟨m, hm⟩ := k
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm' : m < gc.configs.length := by omega
    by_cases hlt : m + 1 < gc.configs.length
    · have hnext : (⟨m + 1, hlt⟩ : Fin gc.configs.length) = nextIndex gc.configs ⟨m, hm'⟩ := by
        ext; simp [nextIndex, Nat.mod_eq_of_lt hlt]
      rw [show (⟨m + 1, hm⟩ : Fin gc.configs.length) = ⟨m + 1, hlt⟩ from Fin.ext rfl,
          hnext, gc.state_eq_of_ne_moverAt ⟨m, hm'⟩ q (by exact Ne.symm (hq_never ⟨m, hm'⟩))]
      exact ih hm'
    · omega

private theorem config_val_const_at_constMover (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hconst : ∀ k : Fin gc.configs.length, gc.moverAt k = p)
    (q : Fin sys.rs.n) (hq : q ≠ p)
    (k : Fin gc.configs.length) :
    (gc.configs.get k) q = (gc.configs.get ⟨0, gc.configs_length_pos⟩) q := by
  obtain ⟨m, hm⟩ := k
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm' : m < gc.configs.length := by omega
    by_cases hlt : m + 1 < gc.configs.length
    · have hnext : (⟨m + 1, hlt⟩ : Fin gc.configs.length) = nextIndex gc.configs ⟨m, hm'⟩ := by
        ext; simp [nextIndex, Nat.mod_eq_of_lt hlt]
      rw [show (⟨m + 1, hm⟩ : Fin gc.configs.length) = ⟨m + 1, hlt⟩ from Fin.ext rfl,
          hnext, gc.state_eq_of_ne_moverAt ⟨m, hm'⟩ q (by rw [hconst]; exact hq)]
      exact ih hm'
    · omega

/-! ### Case A: Safe processor exists -/

/-- If processor q is at distance ≥ 2 from every mover at every step,
    flipping q creates a bad cycle contradicting convergence. -/
theorem safeProcessor_false
    (_hn : sys.rs.n ≥ 5) (gc : GoodCycle sys) (hconv : converges sys gc)
    (q : Fin sys.rs.n)
    (hq_safe : ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q) :
    False := by
  have hq_never : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ q :=
    fun k => (hq_safe k).1
  have hlq_never : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ left q :=
    fun k => (hq_safe k).2.1
  have hrq_never : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ right q :=
    fun k => (hq_safe k).2.2
  have hq_const : ∀ k : Fin gc.configs.length,
      (gc.configs.get k) q = (gc.configs.get ⟨0, gc.configs_length_pos⟩) q :=
    config_val_const_at_neverMover gc q hq_never
  set v₀ := (gc.configs.get ⟨0, gc.configs_length_pos⟩) q
  obtain ⟨v₁, hv₁⟩ := exists_ne_val q v₀
  set L := gc.configs.length with hL_def
  have hLpos : 0 < L := gc.configs_length_pos
  let shadow : Fin L → Config sys.rs :=
    fun k => flipConfig (gc.configs.get k) q v₁
  have shadow_not_mem : ∀ k : Fin L, shadow k ∉ gc.configs := by
    intro k hmem
    rw [List.mem_iff_get] at hmem
    obtain ⟨j, hj⟩ := hmem
    have h_shadow_q : (shadow k) q = v₁ := flipConfig_at_q _ q v₁
    have h_gc_q : (gc.configs.get j) q = v₀ := hq_const j
    rw [hj] at h_gc_q
    exact hv₁ (h_shadow_q.symm.trans h_gc_q)
  have shadow_priv : ∀ k : Fin L, ∃ p : Fin sys.rs.n,
      privileged sys (shadow k) p ∧ gc.moverAt k = p := by
    intro k
    set p := gc.moverAt k with hp_def
    refine ⟨p, ?_, rfl⟩
    apply privileged_of_same_context gc k _ p rfl
    · exact flipConfig_eq_of_ne _ q v₁ (left p) (by
        intro heq
        have : right q = p := by
          calc right q = right (left p) := by rw [heq]
            _ = p := by simp [right_left_eq_self]
        exact hrq_never k (this ▸ hp_def))
    · exact flipConfig_eq_of_ne _ q v₁ p (hq_never k)
    · exact flipConfig_eq_of_ne _ q v₁ (right p) (by
        intro heq
        have : left q = p := by
          calc left q = left (right p) := by rw [heq]
            _ = p := by simp [left_right_eq_self]
        exact hlq_never k (this ▸ hp_def))
  have nextIndex_eq : ∀ k : Fin L,
      nextIndex gc.configs k = ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩ := by
    intro k; rfl
  have shadow_step : ∀ k : Fin L,
      move sys (shadow k) (gc.moverAt k) =
        shadow ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩ := by
    intro k
    set p := gc.moverAt k with hp_def
    have hL_eq : (shadow k) (left p) = (gc.configs.get k) (left p) := by
      exact flipConfig_eq_of_ne _ q v₁ _ (by
        intro heq; have : right q = p := by
          calc right q = right (left p) := by rw [heq]
            _ = p := by simp [right_left_eq_self]
        exact hrq_never k (this ▸ hp_def))
    have hS_eq : (shadow k) p = (gc.configs.get k) p :=
      flipConfig_eq_of_ne _ q v₁ _ (hq_never k)
    have hR_eq : (shadow k) (right p) = (gc.configs.get k) (right p) := by
      exact flipConfig_eq_of_ne _ q v₁ _ (by
        intro heq; have : left q = p := by
          calc left q = left (right p) := by rw [heq]
            _ = p := by simp [left_right_eq_self]
        exact hlq_never k (this ▸ hp_def))
    have hstep := gc.step_eq_move k
    rw [nextIndex_eq] at hstep
    funext j
    by_cases hjp : j = p
    · subst hjp
      calc (move sys (shadow k) p) p
          = (move sys (gc.configs.get k) p) p := by
            simp only [move, hL_eq, hS_eq, hR_eq]
        _ = (gc.configs.get ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩) p := by
            exact (congrFun hstep p).symm
        _ = (flipConfig (gc.configs.get ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩) q v₁) p := by
            exact (flipConfig_eq_of_ne _ q v₁ _ (hq_never k)).symm
    · rw [move_ne_eq (shadow k) p j hjp]
      show (flipConfig (gc.configs.get k) q v₁) j =
           (flipConfig (gc.configs.get ⟨(k.val + 1) % L, _⟩) q v₁) j
      by_cases hjq : j = q
      · subst hjq; rw [flipConfig_at_q, flipConfig_at_q]
      · rw [flipConfig_eq_of_ne _ q v₁ j hjq, flipConfig_eq_of_ne _ q v₁ j hjq]
        have := gc.state_eq_of_ne_moverAt k j (by exact hjp)
        rw [nextIndex_eq] at this
        exact this.symm
  have hbadStep : ∀ k : Fin L,
      badStep sys gc (shadow ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩) (shadow k) := by
    intro k
    obtain ⟨p, hpriv, hp_eq⟩ := shadow_priv k
    refine ⟨shadow_not_mem k,
            shadow_not_mem ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩,
            ⟨p, hpriv, ?_⟩⟩
    rw [← hp_eq]
    exact (shadow_step k).symm
  have hacc : Acc (badStep sys gc) (shadow ⟨0, hLpos⟩) := hconv.apply _
  exact not_acc_of_finite_cycle hLpos shadow
    (fun k => hbadStep k) ⟨0, hLpos⟩ hacc

/-! ### Case B: Zero winding, cw = 0 (all-stay) -/

private theorem moverAt_const_of_allStay (gc : GoodCycle sys)
    (hallStay : ∀ k : Fin gc.configs.length, gc.stepDir k = .stay)
    (k : Fin gc.configs.length) :
    gc.moverAt k = gc.moverAt ⟨0, gc.configs_length_pos⟩ := by
  obtain ⟨m, hm⟩ := k
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm' : m < gc.configs.length := by omega
    have hstep : gc.moverAt ⟨m + 1, hm⟩ = gc.moverAt ⟨m, hm'⟩ := by
      have hstay := hallStay ⟨m, hm'⟩
      have heq := gc.eq_self_of_stepDir_eq_stay hstay
      by_cases hlt : m + 1 < gc.configs.length
      · have hnext : nextIndex gc.configs ⟨m, hm'⟩ = ⟨m + 1, hlt⟩ := by
          ext; simp [nextIndex, Nat.mod_eq_of_lt hlt]
        rw [hnext] at heq
        convert heq using 2
      · omega
    rw [hstep]
    exact ih hm'

private theorem allStay_of_cwZero_ccwZero (gc : GoodCycle sys)
    (hcw : gc.cwStepCount = 0) (hccw : gc.ccwStepCount = 0) :
    ∀ k : Fin gc.configs.length, gc.stepDir k = .stay := by
  intro k
  rcases gc.stepDir_cases k with h | h | h
  · exfalso
    have : gc.cwStepCount ≥ 1 := by
      unfold GoodCycle.cwStepCount
      calc (∑ j : Fin gc.configs.length, if gc.stepDir j = .cw then 1 else 0)
          ≥ (if gc.stepDir k = .cw then 1 else 0) :=
            Finset.single_le_sum (f := fun j => if gc.stepDir j = .cw then 1 else 0)
              (fun j _ => by simp only []; split <;> omega) (Finset.mem_univ k)
        _ = 1 := by simp [h]
    omega
  · exact h
  · exfalso
    have : gc.ccwStepCount ≥ 1 := by
      unfold GoodCycle.ccwStepCount
      calc (∑ j : Fin gc.configs.length, if gc.stepDir j = .ccw then 1 else 0)
          ≥ (if gc.stepDir k = .ccw then 1 else 0) :=
            Finset.single_le_sum (f := fun j => if gc.stepDir j = .ccw then 1 else 0)
              (fun j _ => by simp only []; split <;> omega) (Finset.mem_univ k)
        _ = 1 := by simp [h]
    omega

private theorem fireCount_eq_length_of_constantMover (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hconst : ∀ k : Fin gc.configs.length, gc.moverAt k = p) :
    gc.fireCount p = gc.configs.length := by
  rw [gc.fireCount_eq_sum_moverAt p]
  simp [hconst]

/-- Zero-winding with cw = 0: a single processor fires at every step.
    Flip a far processor → shadow trap → contradiction. -/
theorem zeroWinding_cw0_false
    (hn : sys.rs.n ≥ 5) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hzero : gc.zeroWinding) (hcw0 : gc.cwStepCount = 0) : False := by
  have hccw0 : gc.ccwStepCount = 0 := by
    have heq := gc.cwStepCount_eq_ccwStepCount_of_zeroWinding hzero
    omega
  have hallStay := allStay_of_cwZero_ccwZero gc hcw0 hccw0
  set p := gc.moverAt ⟨0, gc.configs_length_pos⟩ with hp_def
  have hconst : ∀ k : Fin gc.configs.length, gc.moverAt k = p :=
    moverAt_const_of_allStay gc hallStay
  obtain ⟨q, hqp, hqlp, hqrp, hlqp, hrqp⟩ := exists_far_processor hn p
  have hq_const : ∀ k : Fin gc.configs.length,
      (gc.configs.get k) q = (gc.configs.get ⟨0, gc.configs_length_pos⟩) q :=
    config_val_const_at_constMover gc p hconst q hqp
  set v₀ := (gc.configs.get ⟨0, gc.configs_length_pos⟩) q
  obtain ⟨v₁, hv₁⟩ := exists_ne_val q v₀
  set L := gc.configs.length with hL_def
  have hLpos : 0 < L := gc.configs_length_pos
  let shadow : Fin L → Config sys.rs :=
    fun k => flipConfig (gc.configs.get k) q v₁
  have shadow_not_mem : ∀ k : Fin L, shadow k ∉ gc.configs := by
    intro k hmem
    rw [List.mem_iff_get] at hmem
    obtain ⟨j, hj⟩ := hmem
    have h_shadow_q : (shadow k) q = v₁ := flipConfig_at_q _ q v₁
    have h_gc_q : (gc.configs.get j) q = v₀ := hq_const j
    rw [hj] at h_gc_q
    exact hv₁ (h_shadow_q.symm.trans h_gc_q)
  have shadow_priv : ∀ k : Fin L, privileged sys (shadow k) p := by
    intro k
    apply privileged_of_same_context gc k _ p (hconst k)
    · exact flipConfig_eq_of_ne _ q v₁ (left p) (Ne.symm hqlp)
    · exact flipConfig_eq_of_ne _ q v₁ p (Ne.symm hqp)
    · exact flipConfig_eq_of_ne _ q v₁ (right p) (Ne.symm hqrp)
  have nextIndex_eq : ∀ k : Fin L,
      nextIndex gc.configs k = ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩ := by
    intro k; rfl
  have shadow_step : ∀ k : Fin L,
      move sys (shadow k) p = shadow ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩ := by
    intro k
    funext j
    by_cases hjp : j = p
    · subst hjp
      have hL_eq : (shadow k) (left p) = (gc.configs.get k) (left p) :=
        flipConfig_eq_of_ne _ q v₁ _ (Ne.symm hqlp)
      have hS_eq : (shadow k) p = (gc.configs.get k) p :=
        flipConfig_eq_of_ne _ q v₁ _ (Ne.symm hqp)
      have hR_eq : (shadow k) (right p) = (gc.configs.get k) (right p) :=
        flipConfig_eq_of_ne _ q v₁ _ (Ne.symm hqrp)
      have hstep := gc.step_eq_move k
      rw [hconst k] at hstep
      rw [nextIndex_eq] at hstep
      calc (move sys (shadow k) p) p
          = (move sys (gc.configs.get k) p) p := by
            simp only [move, hL_eq, hS_eq, hR_eq]
        _ = (gc.configs.get ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩) p := by
            exact (congrFun hstep p).symm
        _ = (flipConfig (gc.configs.get ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩) q v₁) p := by
            exact (flipConfig_eq_of_ne _ q v₁ _ (Ne.symm hqp)).symm
    · rw [move_ne_eq (shadow k) p j hjp]
      show (flipConfig (gc.configs.get k) q v₁) j =
           (flipConfig (gc.configs.get ⟨(k.val + 1) % L, _⟩) q v₁) j
      by_cases hjq : j = q
      · subst hjq
        rw [flipConfig_at_q, flipConfig_at_q]
      · rw [flipConfig_eq_of_ne _ q v₁ j hjq, flipConfig_eq_of_ne _ q v₁ j hjq]
        have := gc.state_eq_of_ne_moverAt k j (by rw [hconst]; exact hjp)
        rw [nextIndex_eq] at this
        exact this.symm
  have hbadStep : ∀ k : Fin L,
      badStep sys gc (shadow ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩) (shadow k) := by
    intro k
    refine ⟨shadow_not_mem k,
            shadow_not_mem ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩,
            ⟨p, shadow_priv k, (shadow_step k).symm⟩⟩
  have hacc : Acc (badStep sys gc) (shadow ⟨0, hLpos⟩) := hconv.apply _
  exact not_acc_of_finite_cycle hLpos shadow
    (fun k => hbadStep k) ⟨0, hLpos⟩ hacc

/-! ### Safe processor implies zero winding (helper for CaseDispatch) -/

private theorem cwMoveCountAt_eq_zero_of_neverMover (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hp : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ p) :
    gc.cwMoveCountAt p = 0 := by
  unfold GoodCycle.cwMoveCountAt
  apply Finset.sum_eq_zero
  intro k _
  have hne : gc.moverAt k ≠ p := hp k
  simp [hne]

private theorem ccwMoveCountAt_eq_zero_of_neverMover (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hp : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ p) :
    gc.ccwMoveCountAt p = 0 := by
  unfold GoodCycle.ccwMoveCountAt
  apply Finset.sum_eq_zero
  intro k _
  have hne : gc.moverAt k ≠ p := hp k
  simp [hne]

theorem safeProcessor_implies_zeroWinding (gc : GoodCycle sys)
    (q : Fin sys.rs.n)
    (hq_safe : ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q) :
    gc.zeroWinding := by
  unfold GoodCycle.zeroWinding
  have hq_never : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ q :=
    fun k => (hq_safe k).1
  have hrq_never : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ right q :=
    fun k => (hq_safe k).2.2
  have hcw0 : gc.cwMoveCountAt q = 0 :=
    cwMoveCountAt_eq_zero_of_neverMover gc q hq_never
  have hccw0 : gc.ccwMoveCountAt (right q) = 0 :=
    ccwMoveCountAt_eq_zero_of_neverMover gc (right q) hrq_never
  have hflow0 : gc.edgeNetFlow q = 0 := by
    unfold GoodCycle.edgeNetFlow
    simp [hcw0, hccw0]
  rw [gc.totalDisplacement_eq_n_mul_edgeNetFlow q, hflow0]
  simp

end LeanMn
