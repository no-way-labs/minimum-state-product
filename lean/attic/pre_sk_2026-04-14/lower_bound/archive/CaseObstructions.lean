import LeanMn.LowerBound.CycleTypes
import LeanMn.LowerBound.Archive.EntryConflict.GlobalMinGap
import LeanMn.LowerBound.EntryConflict.NonConsecutive
import LeanMn.LowerBound.Archive.EntryConflict.ConsecutiveBinaryEC
import LeanMn.LowerBound.Archive.EntryConflict.PhaseExtraction
import LeanMn.LowerBound.Shadow.Theorem

namespace LeanMn

variable {sys : System}

/-! ### fireCount ≠ 1 -/

-- fireCount_ne_one is now imported from FireCountNe via GlobalMinGap → NestedFirings → FireCountNe

/-! ### All-stay contradicts convergence -/

/-- If every step direction is stay, then the mover at step k equals the mover at step 0,
    for all k. -/
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
      -- stepDir at ⟨m, hm'⟩ is stay, so nextIndex mover = same mover
      have hstay := hallStay ⟨m, hm'⟩
      have heq := gc.eq_self_of_stepDir_eq_stay hstay
      -- nextIndex ⟨m, hm'⟩ = ⟨(m+1) % L, _⟩
      -- If m+1 < L, this is ⟨m+1, _⟩ = ⟨m+1, hm⟩
      by_cases hlt : m + 1 < gc.configs.length
      · have hnext : nextIndex gc.configs ⟨m, hm'⟩ = ⟨m + 1, hlt⟩ := by
          ext; simp [nextIndex, Nat.mod_eq_of_lt hlt]
        rw [hnext] at heq
        convert heq using 2
      · -- m + 1 = gc.configs.length, so nextIndex wraps to 0
        -- But k.val = m + 1 < gc.configs.length = m + 1, contradiction
        omega
    rw [hstep]
    exact ih hm'

/-- If cw and ccw step counts are both zero, then every step is a stay. -/
private theorem allStay_of_cwZero_ccwZero (gc : GoodCycle sys)
    (hcw : gc.cwStepCount = 0) (hccw : gc.ccwStepCount = 0) :
    ∀ k : Fin gc.configs.length, gc.stepDir k = .stay := by
  intro k
  rcases gc.stepDir_cases k with h | h | h
  · -- cw case: contradicts cwStepCount = 0
    exfalso
    have : gc.cwStepCount ≥ 1 := by
      unfold GoodCycle.cwStepCount
      calc (∑ j : Fin gc.configs.length, if gc.stepDir j = .cw then 1 else 0)
          ≥ (if gc.stepDir k = .cw then 1 else 0) :=
            Finset.single_le_sum (f := fun j => if gc.stepDir j = .cw then 1 else 0)
              (fun j _ => by simp only []; split <;> omega) (Finset.mem_univ k)
        _ = 1 := by simp [h]
    omega
  · exact h
  · -- ccw case: contradicts ccwStepCount = 0
    exfalso
    have : gc.ccwStepCount ≥ 1 := by
      unfold GoodCycle.ccwStepCount
      calc (∑ j : Fin gc.configs.length, if gc.stepDir j = .ccw then 1 else 0)
          ≥ (if gc.stepDir k = .ccw then 1 else 0) :=
            Finset.single_le_sum (f := fun j => if gc.stepDir j = .ccw then 1 else 0)
              (fun j _ => by simp only []; split <;> omega) (Finset.mem_univ k)
        _ = 1 := by simp [h]
    omega

/-- If moverAt is constant at p, then fireCount p = configs.length. -/
private theorem fireCount_eq_length_of_constantMover (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hconst : ∀ k : Fin gc.configs.length, gc.moverAt k = p) :
    gc.fireCount p = gc.configs.length := by
  rw [gc.fireCount_eq_sum_moverAt p]
  simp [hconst]

/-- If moverAt is constant at p, then the value at any other processor q is the same
    in all configs. -/
private theorem config_val_const_at_nonMover (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hconst : ∀ k : Fin gc.configs.length, gc.moverAt k = p)
    (q : Fin sys.rs.n) (hq : q ≠ p)
    (k : Fin gc.configs.length) :
    (gc.configs.get k) q = (gc.configs.get ⟨0, gc.configs_length_pos⟩) q := by
  obtain ⟨m, hm⟩ := k
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm' : m < gc.configs.length := by omega
    -- configs.get ⟨m+1, hm⟩ = configs.get (nextIndex ⟨m, hm'⟩) when m+1 < L
    by_cases hlt : m + 1 < gc.configs.length
    · have hnext : (⟨m + 1, hlt⟩ : Fin gc.configs.length) = nextIndex gc.configs ⟨m, hm'⟩ := by
        ext; simp [nextIndex, Nat.mod_eq_of_lt hlt]
      rw [show (⟨m + 1, hm⟩ : Fin gc.configs.length) = ⟨m + 1, hlt⟩ from Fin.ext rfl,
          hnext, gc.state_eq_of_ne_moverAt ⟨m, hm'⟩ q (by rw [hconst]; exact hq)]
      exact ih hm'
    · -- m+1 = L, so ⟨m+1, hm⟩ requires hm : m + 1 < L. But ¬(m+1 < L). Contradiction.
      omega

/-- With n ≥ 5, for any processor p, there exists a processor q that is far from p:
    q ≠ p, q ≠ left p, q ≠ right p, left q ≠ p, right q ≠ p.
    (Equivalently, q is at ring distance ≥ 2 from p.) -/
private theorem exists_far_processor (hn : sys.rs.n ≥ 5) (p : Fin sys.rs.n) :
    ∃ q : Fin sys.rs.n, q ≠ p ∧ q ≠ left p ∧ q ≠ right p ∧
      left q ≠ p ∧ right q ≠ p := by
  -- p, left p, right p, left(left p), right(right p) are at most 5 distinct values
  -- With n ≥ 5, there's room for another processor
  -- We need q with: q ∉ {p, left p, right p} and left q ≠ p and right q ≠ p
  -- left q ≠ p ↔ q ≠ right p (since left q = p → q = right p)
  -- right q ≠ p ↔ q ≠ left p (since right q = p → q = left p)
  -- So the conditions reduce to: q ≠ p, q ≠ left p, q ≠ right p
  -- which is q ∉ {p, left p, right p}
  -- With n ≥ 5, Finset.univ has ≥ 5 elements, and {p, left p, right p} has ≤ 3
  -- So there exists q not in the set
  -- Find q ∉ {p, left p, right p} using Fintype cardinality
  -- With n ≥ 5 and at most 3 neighbors, some processor is far
  obtain ⟨q, hq_ne_p, hq_ne_lp, hq_ne_rp⟩ :
      ∃ q : Fin sys.rs.n, q ≠ p ∧ q ≠ left p ∧ q ≠ right p := by
    by_contra hall
    push_neg at hall
    -- Every processor is in {p, left p, right p}
    have htri : ∀ x : Fin sys.rs.n, x = p ∨ x = left p ∨ x = right p := by
      intro x; by_contra hx; push_neg at hx
      exact hx.2.2 (hall x hx.1 hx.2.1)
    -- This gives n distinct values mapping into a 3-element set
    -- Use Fintype.card_le_of_injective on the identity function
    -- Actually, just use Finset.univ ⊆ {p, left p, right p}
    have hsub : (Finset.univ : Finset (Fin sys.rs.n)) ⊆ {p, left p, right p} := by
      intro x _; simp only [Finset.mem_insert, Finset.mem_singleton]; exact htri x
    have hle := Finset.card_le_card hsub
    rw [Finset.card_fin] at hle
    -- Need |{p, left p, right p}| ≤ 3, which follows from it being a 3-element Finset literal
    -- Finset.card_insert_le : (insert a s).card ≤ s.card + 1
    -- Finset.card_singleton : {a}.card = 1
    have h3 : ({p, left p, right p} : Finset (Fin sys.rs.n)).card ≤ 3 := by
      -- {p, left p, right p} has at most 3 elements
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

/-- Flipping a config at position q to value v. -/
private noncomputable def flipConfig (c : Config sys.rs) (q : Fin sys.rs.n)
    (v : Fin (sys.rs.m q)) : Config sys.rs :=
  fun j => if h : j = q then h ▸ v else c j

/-- The flipped config agrees with the original at all positions except q. -/
private theorem flipConfig_eq_of_ne (c : Config sys.rs) (q : Fin sys.rs.n)
    (v : Fin (sys.rs.m q)) (j : Fin sys.rs.n) (hj : j ≠ q) :
    flipConfig c q v j = c j := by
  simp [flipConfig, hj]

/-- The flipped config has value v at position q. -/
private theorem flipConfig_at_q (c : Config sys.rs) (q : Fin sys.rs.n)
    (v : Fin (sys.rs.m q)) :
    flipConfig c q v q = v := by
  simp [flipConfig]

/-- Moving at processor p doesn't affect position q when q ≠ p. -/
private theorem move_ne_eq (c : Config sys.rs) (p q : Fin sys.rs.n) (hq : q ≠ p) :
    (move sys c p) q = c q := by
  simp [move, hq]

/-- No finite cycle in a well-founded relation: if elements cycle, no element is accessible. -/
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

/-- Processor p is privileged at a config that agrees with a good-cycle config
    at p's neighborhood. -/
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

/-- With n ≥ 2, every processor state space has an alternate value. -/
private theorem exists_ne_val (q : Fin sys.rs.n) (v : Fin (sys.rs.m q)) :
    ∃ v' : Fin (sys.rs.m q), v' ≠ v := by
  have hm : 2 ≤ sys.rs.m q := sys.rs.m_pos q
  have hvlt := v.isLt
  have hlt : (v.val + 1) % sys.rs.m q < sys.rs.m q := Nat.mod_lt _ (by omega)
  refine ⟨⟨(v.val + 1) % sys.rs.m q, hlt⟩, ?_⟩
  intro h
  have hval : (v.val + 1) % sys.rs.m q = v.val := congrArg Fin.val h
  -- (v.val + 1) % m = v.val implies m | 1, so m ≤ 1, contradicting m ≥ 2
  have : (v.val + 1) % sys.rs.m q ≠ v.val := by
    by_cases hvmax : v.val + 1 < sys.rs.m q
    · rw [Nat.mod_eq_of_lt hvmax]; omega
    · rw [show v.val + 1 = sys.rs.m q from by omega, Nat.mod_self]; omega
  exact this hval

/-- All-stay zero-winding good cycles contradict convergence.

    If a good cycle has zero winding and no clockwise steps (hence no counterclockwise
    steps either), then every step is a "stay" — the mover doesn't change. This means
    a single processor p fires at every step. We construct a cycle of bad configurations
    by flipping a far-away processor q's value: since q never fires, the flipped configs
    mirror the good cycle but differ at q, creating an infinite chain of bad transitions
    that contradicts well-foundedness. -/
theorem all_stay_contradicts_convergence
    (hn : sys.rs.n ≥ 5) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hzero : gc.zeroWinding) (hcw0 : gc.cwStepCount = 0) : False := by
  -- Step 1: derive ccwStepCount = 0 from zeroWinding + cwStepCount = 0
  have hccw0 : gc.ccwStepCount = 0 := by
    have heq := gc.cwStepCount_eq_ccwStepCount_of_zeroWinding hzero
    omega
  -- Step 2: all steps are stay
  have hallStay := allStay_of_cwZero_ccwZero gc hcw0 hccw0
  -- Step 3: moverAt is constant
  set p := gc.moverAt ⟨0, gc.configs_length_pos⟩ with hp_def
  have hconst : ∀ k : Fin gc.configs.length, gc.moverAt k = p :=
    moverAt_const_of_allStay gc hallStay
  -- Step 4: find a far processor q
  obtain ⟨q, hqp, hqlp, hqrp, hlqp, hrqp⟩ := exists_far_processor hn p
  -- Step 5: q's value is constant throughout the good cycle
  have hq_const : ∀ k : Fin gc.configs.length,
      (gc.configs.get k) q = (gc.configs.get ⟨0, gc.configs_length_pos⟩) q :=
    config_val_const_at_nonMover gc p hconst q hqp
  -- Step 6: find an alternate value for q
  set v₀ := (gc.configs.get ⟨0, gc.configs_length_pos⟩) q
  obtain ⟨v₁, hv₁⟩ := exists_ne_val q v₀
  -- Step 7: construct shadow configs
  -- shadow_k = gc.configs[k] with q flipped to v₁
  set L := gc.configs.length with hL_def
  have hLpos : 0 < L := gc.configs_length_pos
  let shadow : Fin L → Config sys.rs :=
    fun k => flipConfig (gc.configs.get k) q v₁
  -- Step 8: show each shadow config is not in gc.configs
  have shadow_not_mem : ∀ k : Fin L, shadow k ∉ gc.configs := by
    intro k hmem
    -- shadow k is in gc.configs, so shadow k = gc.configs.get j for some j
    rw [List.mem_iff_get] at hmem
    obtain ⟨j, hj⟩ := hmem
    -- hj : gc.configs.get j = shadow k
    -- At position q: shadow k q = v₁ but gc.configs.get j q = v₀
    have h_shadow_q : (shadow k) q = v₁ := flipConfig_at_q _ q v₁
    have h_gc_q : (gc.configs.get j) q = v₀ := hq_const j
    -- From hj: (gc.configs.get j) q = (shadow k) q
    rw [hj] at h_gc_q
    -- Now h_gc_q : (shadow k) q = v₀ and h_shadow_q : (shadow k) q = v₁
    exact hv₁ (h_shadow_q.symm.trans h_gc_q)
  -- Step 9: show p is privileged at each shadow config
  have shadow_priv : ∀ k : Fin L, privileged sys (shadow k) p := by
    intro k
    apply privileged_of_same_context gc k _ p (hconst k)
    · exact flipConfig_eq_of_ne _ q v₁ (left p) (Ne.symm hqlp)
    · exact flipConfig_eq_of_ne _ q v₁ p (Ne.symm hqp)
    · exact flipConfig_eq_of_ne _ q v₁ (right p) (Ne.symm hqrp)
  -- Step 10: show move sys (shadow k) p = shadow (k+1 mod L)
  -- Helper: nextIndex equivalence
  have nextIndex_eq : ∀ k : Fin L,
      nextIndex gc.configs k = ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩ := by
    intro k; rfl
  have shadow_step : ∀ k : Fin L,
      move sys (shadow k) p = shadow ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩ := by
    intro k
    funext j
    by_cases hjp : j = p
    · -- At p: both sides equal the transition function output
      subst hjp
      -- Shadow k and gc.configs.get k agree at p's local neighborhood
      have hL_eq : (shadow k) (left p) = (gc.configs.get k) (left p) :=
        flipConfig_eq_of_ne _ q v₁ _ (Ne.symm hqlp)
      have hS_eq : (shadow k) p = (gc.configs.get k) p :=
        flipConfig_eq_of_ne _ q v₁ _ (Ne.symm hqp)
      have hR_eq : (shadow k) (right p) = (gc.configs.get k) (right p) :=
        flipConfig_eq_of_ne _ q v₁ _ (Ne.symm hqrp)
      -- From good cycle step: gc.configs.get(nextIndex k) = move sys (gc.configs.get k) p
      have hstep := gc.step_eq_move k
      rw [hconst k] at hstep
      rw [nextIndex_eq] at hstep
      -- hstep : gc.configs.get ⟨(k+1)%L, _⟩ = move sys (gc.configs.get k) p
      -- The chain: LHS = (move shadow) p = (move gc) p = gc.get(k+1) p = (flipConfig gc.get(k+1)) p = RHS
      -- Step A: (move sys (shadow k) p) p = (move sys (gc.configs.get k) p) p
      -- Step B: (move sys (gc.configs.get k) p) p = (gc.configs.get ⟨(k+1)%L, _⟩) p (from hstep)
      -- Step C: (gc.configs.get ⟨(k+1)%L, _⟩) p = (flipConfig (gc.configs.get ⟨(k+1)%L, _⟩) q v₁) p (flip at p is identity since p ≠ q)
      -- Combine into a calc proof
      calc (move sys (shadow k) p) p
          = (move sys (gc.configs.get k) p) p := by
            simp only [move, hL_eq, hS_eq, hR_eq]
        _ = (gc.configs.get ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩) p := by
            exact (congrFun hstep p).symm
        _ = (flipConfig (gc.configs.get ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩) q v₁) p := by
            exact (flipConfig_eq_of_ne _ q v₁ _ (Ne.symm hqp)).symm
    · -- At j ≠ p: move doesn't change j
      rw [move_ne_eq (shadow k) p j hjp]
      -- Goal: (shadow k) j = (shadow ⟨(k.val + 1) % L, _⟩) j
      -- Both are flipConfig of gc configs at j
      -- shadow k = flipConfig (gc.configs.get k) q v₁
      -- shadow (k+1) = flipConfig (gc.configs.get (k+1)) q v₁
      show (flipConfig (gc.configs.get k) q v₁) j =
           (flipConfig (gc.configs.get ⟨(k.val + 1) % L, _⟩) q v₁) j
      by_cases hjq : j = q
      · -- At q: both are v₁
        subst hjq
        rw [flipConfig_at_q, flipConfig_at_q]
      · -- At j ≠ q: both equal the gc config value at j
        rw [flipConfig_eq_of_ne _ q v₁ j hjq, flipConfig_eq_of_ne _ q v₁ j hjq]
        -- gc values at j are constant across steps (j ≠ p = mover)
        have := gc.state_eq_of_ne_moverAt k j (by rw [hconst]; exact hjp)
        rw [nextIndex_eq] at this
        exact this.symm
  -- Step 11: construct the bad cycle
  have hbadStep : ∀ k : Fin L,
      badStep sys gc (shadow ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩) (shadow k) := by
    intro k
    refine ⟨shadow_not_mem k,
            shadow_not_mem ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩,
            ⟨p, shadow_priv k, (shadow_step k).symm⟩⟩
  -- Step 12: derive contradiction from WellFounded
  have hacc : Acc (badStep sys gc) (shadow ⟨0, hLpos⟩) := hconv.apply _
  exact not_acc_of_finite_cycle hLpos shadow
    (fun k => hbadStep k) ⟨0, hLpos⟩ hacc

/-! ### Small-arc contradicts convergence -/

/-- If processor q is never the mover at any step, then q's value is constant
    across all configs in the good cycle. -/
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

/-- If q is at distance ≥ 2 from every mover position in the cycle,
    the same parallel-orbit argument as `all_stay_contradicts_convergence`
    applies: flipping q produces a cycle of bad configs, contradicting
    well-foundedness.

    This generalises `all_stay_contradicts_convergence` from "mover visits
    exactly 1 processor" to "there exists a processor q that is never the
    mover and never adjacent to the mover". -/
theorem small_arc_contradicts_convergence
    (_hn : sys.rs.n ≥ 4) (gc : GoodCycle sys) (hconv : converges sys gc)
    (q : Fin sys.rs.n)
    (hq_safe : ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q) :
    False := by
  -- Extract the three components of hq_safe
  have hq_never : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ q :=
    fun k => (hq_safe k).1
  have hlq_never : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ left q :=
    fun k => (hq_safe k).2.1
  have hrq_never : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ right q :=
    fun k => (hq_safe k).2.2
  -- Step 1: q's value is constant throughout the cycle
  have hq_const : ∀ k : Fin gc.configs.length,
      (gc.configs.get k) q = (gc.configs.get ⟨0, gc.configs_length_pos⟩) q :=
    config_val_const_at_neverMover gc q hq_never
  -- Step 2: find an alternate value for q
  set v₀ := (gc.configs.get ⟨0, gc.configs_length_pos⟩) q
  obtain ⟨v₁, hv₁⟩ := exists_ne_val q v₀
  -- Step 3: construct shadow configs
  set L := gc.configs.length with hL_def
  have hLpos : 0 < L := gc.configs_length_pos
  let shadow : Fin L → Config sys.rs :=
    fun k => flipConfig (gc.configs.get k) q v₁
  -- Step 4: show each shadow config is not in gc.configs
  have shadow_not_mem : ∀ k : Fin L, shadow k ∉ gc.configs := by
    intro k hmem
    rw [List.mem_iff_get] at hmem
    obtain ⟨j, hj⟩ := hmem
    have h_shadow_q : (shadow k) q = v₁ := flipConfig_at_q _ q v₁
    have h_gc_q : (gc.configs.get j) q = v₀ := hq_const j
    rw [hj] at h_gc_q
    exact hv₁ (h_shadow_q.symm.trans h_gc_q)
  -- Step 5: show the mover at each step is privileged at the shadow config
  -- hq_safe gives moverAt k ≠ q/left q/right q.  We need q ≠ moverAt k/left(moverAt k)/right(moverAt k).
  -- q = left(moverAt k) ⟹ right q = moverAt k, contradicting moverAt k ≠ right q.
  -- q = right(moverAt k) ⟹ left q = moverAt k, contradicting moverAt k ≠ left q.
  have shadow_priv : ∀ k : Fin L, ∃ p : Fin sys.rs.n,
      privileged sys (shadow k) p ∧ gc.moverAt k = p := by
    intro k
    set p := gc.moverAt k with hp_def
    refine ⟨p, ?_, rfl⟩
    apply privileged_of_same_context gc k _ p rfl
    · -- left p: need q ≠ left p
      -- Suppose q = left p. Then right q = right (left p) = p.
      -- But moverAt k = p, and hq_safe gives moverAt k ≠ right q. Contradiction.
      exact flipConfig_eq_of_ne _ q v₁ (left p) (by
        intro heq
        have : right q = p := by
          calc right q = right (left p) := by rw [heq]
            _ = p := by simp [right_left_eq_self]
        exact hrq_never k (this ▸ hp_def))
    · -- p itself: need p ≠ q
      exact flipConfig_eq_of_ne _ q v₁ p (hq_never k)
    · -- right p: need q ≠ right p
      -- Suppose q = right p. Then left q = left (right p) = p.
      -- But moverAt k = p, and hq_safe gives moverAt k ≠ left q. Contradiction.
      exact flipConfig_eq_of_ne _ q v₁ (right p) (by
        intro heq
        have : left q = p := by
          calc left q = left (right p) := by rw [heq]
            _ = p := by simp [left_right_eq_self]
        exact hlq_never k (this ▸ hp_def))
  -- Step 6: show move sys (shadow k) (moverAt k) = shadow (nextIndex k)
  have nextIndex_eq : ∀ k : Fin L,
      nextIndex gc.configs k = ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩ := by
    intro k; rfl
  have shadow_step : ∀ k : Fin L,
      move sys (shadow k) (gc.moverAt k) =
        shadow ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩ := by
    intro k
    set p := gc.moverAt k with hp_def
    -- Shadow k and gc.configs.get k agree at p's neighborhood
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
  -- Step 7: construct the bad cycle
  have hbadStep : ∀ k : Fin L,
      badStep sys gc (shadow ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩) (shadow k) := by
    intro k
    obtain ⟨p, hpriv, hp_eq⟩ := shadow_priv k
    refine ⟨shadow_not_mem k,
            shadow_not_mem ⟨(k.val + 1) % L, Nat.mod_lt _ hLpos⟩,
            ⟨p, hpriv, ?_⟩⟩
    rw [← hp_eq]
    exact (shadow_step k).symm
  -- Step 8: derive contradiction from WellFounded
  have hacc : Acc (badStep sys gc) (shadow ⟨0, hLpos⟩) := hconv.apply _
  exact not_acc_of_finite_cycle hLpos shadow
    (fun k => hbadStep k) ⟨0, hLpos⟩ hacc

/-! ### Safe processor implies zero winding (proved) -/

/-- If processor p never fires, its cwMoveCountAt is zero. -/
private theorem cwMoveCountAt_eq_zero_of_neverMover (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hp : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ p) :
    gc.cwMoveCountAt p = 0 := by
  unfold GoodCycle.cwMoveCountAt
  apply Finset.sum_eq_zero
  intro k _
  have hne : gc.moverAt k ≠ p := hp k
  simp [hne]

/-- If processor p never fires, its ccwMoveCountAt is zero. -/
private theorem ccwMoveCountAt_eq_zero_of_neverMover (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hp : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ p) :
    gc.ccwMoveCountAt p = 0 := by
  unfold GoodCycle.ccwMoveCountAt
  apply Finset.sum_eq_zero
  intro k _
  have hne : gc.moverAt k ≠ p := hp k
  simp [hne]

/-- If a safe processor exists (q, left q, right q are never movers),
    then the edge net flow at q is zero. Combined with edgeNetFlow being
    constant, this gives totalDisplacement = 0 (zero winding).

    Proof: edgeNetFlow q = cwMoveCountAt q - ccwMoveCountAt (right q).
    Since q never fires, cwMoveCountAt q = 0.
    Since right q never fires, ccwMoveCountAt (right q) = 0.
    So edgeNetFlow q = 0. -/
private theorem edgeNetFlow_eq_zero_of_safeProcessor (gc : GoodCycle sys)
    (q : Fin sys.rs.n)
    (hq_safe : ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q) :
    gc.edgeNetFlow q = 0 := by
  have hq_never : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ q :=
    fun k => (hq_safe k).1
  have hrq_never : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ right q :=
    fun k => (hq_safe k).2.2
  have hcw0 : gc.cwMoveCountAt q = 0 :=
    cwMoveCountAt_eq_zero_of_neverMover gc q hq_never
  have hccw0 : gc.ccwMoveCountAt (right q) = 0 :=
    ccwMoveCountAt_eq_zero_of_neverMover gc (right q) hrq_never
  unfold GoodCycle.edgeNetFlow
  simp [hcw0, hccw0]

/-- **Safe processor implies zero winding (proved).**

    If a processor q exists such that q, left q, and right q are never
    movers, then the good cycle has zero winding (totalDisplacement = 0).

    Proof: edgeNetFlow at q is 0 (since q and right q never fire),
    edgeNetFlow is constant across all edges (CycleTypes.lean), and
    totalDisplacement = n · edgeNetFlow. -/
theorem safeProcessor_implies_zeroWinding (gc : GoodCycle sys)
    (q : Fin sys.rs.n)
    (hq_safe : ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q) :
    gc.zeroWinding := by
  unfold GoodCycle.zeroWinding
  have hflow0 : gc.edgeNetFlow q = 0 :=
    edgeNetFlow_eq_zero_of_safeProcessor gc q hq_safe
  rw [gc.totalDisplacement_eq_n_mul_edgeNetFlow q, hflow0]
  simp

/-- **Contrapositive: non-zero winding implies no safe processor (proved).**

    If a good cycle has non-zero winding, then every processor is within
    distance 1 of some mover position.  This means the mover arc covers
    the entire ring within its 1-neighborhood. -/
theorem no_safeProcessor_of_nonZeroWinding (gc : GoodCycle sys)
    (hnonzero : ¬gc.zeroWinding) :
    ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q := by
  intro ⟨q, hq⟩
  exact hnonzero (safeProcessor_implies_zeroWinding gc q hq)

/-! ### Non-zero-winding sub-case lemmas -/

/-- Absolute displacement is at most the cycle length. Each step contributes
    at most 1 to the displacement sum, so |∑ signedStep| ≤ L. -/
private theorem totalDisplacement_natAbs_le_length (gc : GoodCycle sys) :
    (totalDisplacement gc).natAbs ≤ gc.configs.length := by
  rw [gc.totalDisplacement_eq_cwStepCount_sub_ccwStepCount]
  have hpart := gc.stepCount_partition
  have hle : gc.cwStepCount + gc.ccwStepCount ≤ gc.configs.length := by omega
  omega

/-- A sweep cycle has length at least 2n. -/
private theorem sweep_length_ge (gc : GoodCycle sys) (hsweep : gc.isSweep) :
    gc.configs.length ≥ 2 * sys.rs.n := by
  unfold GoodCycle.isSweep at hsweep
  exact le_trans hsweep (totalDisplacement_natAbs_le_length gc)

/-- A sweep cycle is not zero-winding. -/
private theorem sweep_not_zeroWinding (gc : GoodCycle sys) (hsweep : gc.isSweep)
    (hn : sys.rs.n ≥ 5) : ¬gc.zeroWinding := by
  intro hzw
  unfold GoodCycle.zeroWinding at hzw
  unfold GoodCycle.isSweep at hsweep
  have h0 : (totalDisplacement gc).natAbs = 0 := by rw [hzw]; decide
  omega

/-- Sweep implies |edgeNetFlow| ≥ 2. -/
private theorem sweep_edgeNetFlow_natAbs_ge_two (gc : GoodCycle sys) (hsweep : gc.isSweep)
    (p : Fin sys.rs.n) :
    Int.natAbs (gc.edgeNetFlow p) ≥ 2 := by
  unfold GoodCycle.isSweep at hsweep
  rw [gc.totalDisplacement_eq_n_mul_edgeNetFlow p, Int.natAbs_mul] at hsweep
  have hn_pos : 0 < sys.rs.n := by have := sys.rs.n_ge_4; omega
  have hn_natAbs : Int.natAbs (sys.rs.n : Int) = sys.rs.n := by omega
  rw [hn_natAbs] at hsweep
  -- hsweep : 2 * sys.rs.n ≤ sys.rs.n * (gc.edgeNetFlow p).natAbs
  -- With sys.rs.n > 0, divide both sides
  by_contra hlt
  push_neg at hlt
  have hlt' : Int.natAbs (gc.edgeNetFlow p) ≤ 1 := by omega
  have hmul : sys.rs.n * Int.natAbs (gc.edgeNetFlow p) ≤ sys.rs.n * 1 :=
    Nat.mul_le_mul_left _ hlt'
  linarith

/-- cwMoveCountAt p ≤ fireCount p. -/
private theorem cwMoveCountAt_le_fireCount (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    gc.cwMoveCountAt p ≤ gc.fireCount p := by
  have h := gc.fireCount_eq_moveCount_partition p
  omega

/-- ccwMoveCountAt p ≤ fireCount p. -/
private theorem ccwMoveCountAt_le_fireCount (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    gc.ccwMoveCountAt p ≤ gc.fireCount p := by
  have h := gc.fireCount_eq_moveCount_partition p
  omega

/-- Sweep implies fireCount ≥ 2 for every processor. -/
private theorem sweep_fireCount_ge_two (gc : GoodCycle sys) (hsweep : gc.isSweep)
    (p : Fin sys.rs.n) :
    gc.fireCount p ≥ 2 := by
  have hflow := sweep_edgeNetFlow_natAbs_ge_two gc hsweep p
  -- edgeNetFlow p = cwMoveCountAt p - ccwMoveCountAt (right p)
  -- |edgeNetFlow p| ≥ 2
  -- Case split on sign
  by_cases hpos : gc.edgeNetFlow p ≥ 0
  · -- edgeNetFlow ≥ 0, so edgeNetFlow ≥ 2
    have hge2 : gc.edgeNetFlow p ≥ 2 := by omega
    -- edgeNetFlow p = cwMoveCountAt p - ccwMoveCountAt (right p)
    -- So cwMoveCountAt p ≥ 2 + ccwMoveCountAt (right p) ≥ 2
    unfold GoodCycle.edgeNetFlow at hge2
    have : gc.cwMoveCountAt p ≥ 2 := by omega
    calc gc.fireCount p ≥ gc.cwMoveCountAt p := cwMoveCountAt_le_fireCount gc p
      _ ≥ 2 := this
  · -- edgeNetFlow < 0, so -edgeNetFlow ≥ 2
    push_neg at hpos
    have hle : gc.edgeNetFlow p ≤ -2 := by omega
    -- edgeNetFlow p = cwMoveCountAt p - ccwMoveCountAt (right p) ≤ -2
    -- So ccwMoveCountAt (right p) ≥ cwMoveCountAt p + 2 ≥ 2
    unfold GoodCycle.edgeNetFlow at hle
    have : gc.ccwMoveCountAt (right p) ≥ 2 := by omega
    -- fireCount(right p) ≥ ccwMoveCountAt(right p) ≥ 2
    -- But we need fireCount p, not fireCount (right p)
    -- Use edgeNetFlow constancy: edgeNetFlow (left p) = edgeNetFlow p ≤ -2
    -- So ccwMoveCountAt (right (left p)) = ccwMoveCountAt p ≥ 2
    have hflow_left := gc.edgeNetFlow_constant p (left p)
    have hle' : gc.edgeNetFlow (left p) ≤ -2 := by omega
    unfold GoodCycle.edgeNetFlow at hle'
    have hrlp : right (left p) = p := by simpa using right_left_eq_self p
    rw [hrlp] at hle'
    have : gc.ccwMoveCountAt p ≥ 2 := by omega
    calc gc.fireCount p ≥ gc.ccwMoveCountAt p := ccwMoveCountAt_le_fireCount gc p
      _ ≥ 2 := this

/-- Sweep implies cwStepCount > 0 or ccwStepCount > 0. -/
private theorem sweep_cwOrCcw_pos (gc : GoodCycle sys) (hsweep : gc.isSweep)
    (hn : sys.rs.n ≥ 5) :
    gc.cwStepCount > 0 ∨ gc.ccwStepCount > 0 := by
  have hnzw := sweep_not_zeroWinding gc hsweep hn
  unfold GoodCycle.zeroWinding at hnzw
  rw [gc.totalDisplacement_eq_cwStepCount_sub_ccwStepCount] at hnzw
  by_contra h
  push_neg at h
  rcases h with ⟨hcw, hccw⟩
  have : gc.cwStepCount = 0 := by omega
  have : gc.ccwStepCount = 0 := by omega
  simp_all

/-- Permanent mover (all steps fire p) implies totalDisplacement = 0. -/
private theorem permanent_mover_totalDisplacement_zero (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hperm : ∀ k : Fin gc.configs.length, gc.moverAt k = p) :
    totalDisplacement gc = 0 := by
  rw [gc.totalDisplacement_eq_cwStepCount_sub_ccwStepCount]
  -- All steps have mover = p. CW means next mover = right p ≠ p.
  -- CCW means next mover = left p ≠ p.
  -- But hperm says ALL movers = p. So no CW or CCW steps.
  have hcw0 : gc.cwStepCount = 0 := by
    unfold GoodCycle.cwStepCount
    apply Finset.sum_eq_zero; intro k _
    by_cases hdir : gc.stepDir k = .cw
    · exfalso
      have hnext := gc.eq_right_of_stepDir_eq_cw hdir
      rw [hperm k] at hnext
      have := hperm (nextIndex gc.configs k)
      rw [hnext] at this
      have hval := congrArg Fin.val this
      simp only [right_val] at hval
      have hp := p.isLt; have hn4 := sys.rs.n_ge_4
      by_cases h1 : p.val + 1 < sys.rs.n
      · rw [Nat.mod_eq_of_lt h1] at hval; omega
      · rw [show p.val + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega
    · simp [show ¬(gc.stepDir k = .cw) from hdir]
  have hccw0 : gc.ccwStepCount = 0 := by
    unfold GoodCycle.ccwStepCount
    apply Finset.sum_eq_zero; intro k _
    by_cases hdir : gc.stepDir k = .ccw
    · exfalso
      have hnext := gc.eq_left_of_stepDir_eq_ccw hdir
      rw [hperm k] at hnext
      have := hperm (nextIndex gc.configs k)
      rw [hnext] at this
      have hval := congrArg Fin.val this
      simp only [left_val] at hval
      have hp := p.isLt; have hn4 := sys.rs.n_ge_4
      by_cases h0 : p.val = 0
      · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hval; omega
      · rw [show p.val + sys.rs.n - 1 = (p.val - 1) + sys.rs.n from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hval; omega
    · simp [show ¬(gc.stepDir k = .ccw) from hdir]
  simp [hcw0, hccw0]

/-- **Consecutive binary + isolated firings → False.**

    Shared sub-lemma for sweep and odd-winding cases. When 3 consecutive
    binary {i, ri, rri} exist and ri = right i has fireCount ≥ 2 with all
    isolated firings (no two consecutive ri-fires), the MinFiringGap gap ≥ 2.
    The parity walk argument proves that some gap has even L-fires and
    even R-fires, giving entry conflict.

    BLOCKED: the theorem as stated is too weak — a counterexample exists with
    n=4, 3 consecutive binary, FC(ri)=2, all isolated, and no entry conflict
    (cycle of length 6 visiting 6 of 8 possible local triples).
    The callers (sweep_sub_threshold_false, oddWinding_nonUniform_sub_threshold_false)
    have additional structure (sweep ⟹ L ≥ 2n, odd winding ⟹ L ≥ n, all binary
    procs fire ≥ 2) that prevents this counterexample. The theorem needs
    additional hypotheses such as `∀ p, gc.fireCount p ≥ 1` and `sys.rs.n ≥ 9`
    (which force non-{i,ri,rri} firings in gaps, enabling the step-before
    entry conflict argument). -/
private theorem exists_outside_triple_neighborhood
    (hn : sys.rs.n ≥ 6) (i : Fin sys.rs.n) :
    ∃ q : Fin sys.rs.n,
      q ≠ left i ∧ q ≠ i ∧ q ≠ right i ∧
      q ≠ right (right i) ∧ q ≠ right (right (right i)) := by
  by_contra hall
  push_neg at hall
  have hcover :
      ∀ x : Fin sys.rs.n,
        x = left i ∨ x = i ∨ x = right i ∨
          x = right (right i) ∨ x = right (right (right i)) := by
    intro x
    by_cases hx_li : x = left i
    · exact Or.inl hx_li
    · by_cases hx_i : x = i
      · exact Or.inr (Or.inl hx_i)
      · by_cases hx_ri : x = right i
        · exact Or.inr (Or.inr (Or.inl hx_ri))
        · by_cases hx_rri : x = right (right i)
          · exact Or.inr (Or.inr (Or.inr (Or.inl hx_rri)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (hall x hx_li hx_i hx_ri hx_rri))))
  have hsub :
      (Finset.univ : Finset (Fin sys.rs.n)) ⊆
        ({left i, i, right i, right (right i), right (right (right i))} :
          Finset (Fin sys.rs.n)) := by
    intro x _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hcover x
  have hle := Finset.card_le_card hsub
  rw [Finset.card_fin] at hle
  have h5 :
      ({left i, i, right i, right (right i), right (right (right i))} :
        Finset (Fin sys.rs.n)).card ≤ 5 := by
    let S₁ : Finset (Fin sys.rs.n) := {left i}
    let S₂ : Finset (Fin sys.rs.n) := {i}
    let S₃ : Finset (Fin sys.rs.n) := {right i}
    let S₄ : Finset (Fin sys.rs.n) := {right (right i)}
    let S₅ : Finset (Fin sys.rs.n) := {right (right (right i))}
    let U₁₂ : Finset (Fin sys.rs.n) := S₁ ∪ S₂
    let U₁₂₃ : Finset (Fin sys.rs.n) := U₁₂ ∪ S₃
    let U₁₂₃₄ : Finset (Fin sys.rs.n) := U₁₂₃ ∪ S₄
    let U : Finset (Fin sys.rs.n) := U₁₂₃₄ ∪ S₅
    have hsub5 :
        ({left i, i, right i, right (right i), right (right (right i))} :
          Finset (Fin sys.rs.n)) ⊆ U := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        simp [U, U₁₂₃₄, U₁₂₃, U₁₂, S₁, S₂, S₃, S₄, S₅,
          Finset.mem_union, Finset.mem_singleton]
    calc ({left i, i, right i, right (right i), right (right (right i))} :
          Finset (Fin sys.rs.n)).card
        ≤ U.card :=
            Finset.card_le_card hsub5
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

private theorem safeProcessor_of_mover_subset_triple
    (hn : sys.rs.n ≥ 6) (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (hsubset : ∀ k : Fin gc.configs.length,
      gc.moverAt k = i ∨
      gc.moverAt k = right i ∨
      gc.moverAt k = right (right i)) :
    ∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q := by
  obtain ⟨q, hq_li, hq_i, hq_ri, hq_rri, hq_r3⟩ := exists_outside_triple_neighborhood hn i
  refine ⟨q, ?_⟩
  intro k
  rcases hsubset k with hmov | hmov | hmov
  · refine ⟨?_, ?_, ?_⟩
    · intro hq
      have : q = i := by
        calc q = gc.moverAt k := hq.symm
          _ = i := hmov
      exact hq_i this
    · intro hlq
      have : q = right i := by
        calc q = right (left q) := by simp [right_left_eq_self]
          _ = right (gc.moverAt k) := by rw [hlq]
          _ = right i := by rw [hmov]
      exact hq_ri this
    · intro hrq
      have : q = left i := by
        calc q = left (right q) := by simp [left_right_eq_self]
          _ = left (gc.moverAt k) := by rw [hrq]
          _ = left i := by rw [hmov]
      exact hq_li this
  · refine ⟨?_, ?_, ?_⟩
    · intro hq
      have : q = right i := by
        calc q = gc.moverAt k := hq.symm
          _ = right i := hmov
      exact hq_ri this
    · intro hlq
      have : q = right (right i) := by
        calc q = right (left q) := by simp [right_left_eq_self]
          _ = right (gc.moverAt k) := by rw [hlq]
          _ = right (right i) := by rw [hmov]
      exact hq_rri this
    · intro hrq
      have : q = i := by
        calc q = left (right q) := by simp [left_right_eq_self]
          _ = left (gc.moverAt k) := by rw [hrq]
          _ = left (right i) := by rw [hmov]
          _ = i := by simp [left_right_eq_self]
      exact hq_i this
  · refine ⟨?_, ?_, ?_⟩
    · intro hq
      have : q = right (right i) := by
        calc q = gc.moverAt k := hq.symm
          _ = right (right i) := hmov
      exact hq_rri this
    · intro hlq
      have : q = right (right (right i)) := by
        calc q = right (left q) := by simp [right_left_eq_self]
          _ = right (gc.moverAt k) := by rw [hlq]
          _ = right (right (right i)) := by rw [hmov]
      exact hq_r3 this
    · intro hrq
      have : q = right i := by
        calc q = left (right q) := by simp [left_right_eq_self]
          _ = left (gc.moverAt k) := by rw [hrq]
          _ = left (right (right i)) := by rw [hmov]
          _ = right i := by simp [left_right_eq_self]
      exact hq_ri this

/-- Residual hard case for `consecutive_binary_isolated_false`.

    The confined-mover case is discharged separately by deriving a safe
    processor and applying `small_arc_contradicts_convergence`.  What remains
    is the genuinely nonlocal branch:
    1. no safe processor exists, and
    2. some mover step leaves the local triple {i, right i, right(right i)}.

    This is exactly the case where a "different gap / far mover" extraction
    argument is still needed. -/
private theorem consecutive_binary_isolated_false_noSafe_outsideMover
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (_hconv : converges sys gc)
    (i : Fin sys.rs.n)
    (h3bin : threeConsecutiveBinary sys.rs i)
    (_hfc : gc.fireCount (right i) ≥ 2)
    (_hiso : ∀ (a : Fin gc.configs.length),
      gc.moverAt a = right i → gc.moverAt (nextIndex gc.configs a) ≠ right i)
    (_hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (_houtside : ∃ k : Fin gc.configs.length,
      gc.moverAt k ≠ i ∧
      gc.moverAt k ≠ right i ∧
      gc.moverAt k ≠ right (right i))
    (_hsub : subThreshold sys.rs) (_h3bin_global : hasGe3Binary sys.rs)
    (_hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0) :
    False := by
  -- right i has fc ≥ 2 and fc < L (from outside mover → L > fc(ri))
  have hfc_lt_L : gc.fireCount (right i) < gc.configs.length := by
    obtain ⟨k, _, hk_nri, _⟩ := _houtside
    rw [gc.fireCount_eq_sum_moverAt]
    calc ∑ j : Fin gc.configs.length, (if gc.moverAt j = right i then (1 : Nat) else 0)
        < ∑ j : Fin gc.configs.length, 1 := by
          apply Finset.sum_lt_sum
          · intro j _; split <;> omega
          · exact ⟨k, Finset.mem_univ k, by simp [hk_nri]⟩
      _ = gc.configs.length := by simp
  -- right i has binary left (= i) and binary right (= rri)
  have hbL : sys.rs.m (left (right i)) = 2 := by
    rw [show left (right i) = i from left_right_eq_self i]; exact h3bin.1
  have hbR : sys.rs.m (right (right i)) = 2 := h3bin.2.2
  -- Extract a ternary phase and dispatch directly: mechanism-triggering phases
  -- close via `phase_dispatch_ec`, while the all-normal residual routes through
  -- the shared phase-extraction residue wrapper.
  obtain ⟨phase, _⟩ := exists_ternaryPhase gc (right i) _hfc hfc_lt_L
  by_cases hmech : let J := gc.intervalFireCount (left (right i)) phase.a.val phase.s.val
                   let K := gc.intervalFireCount (right (right i)) phase.a.val phase.s.val
                   (Even J ∧ Even K) ∨ (J ≥ 2 ∧ K = 0) ∨ (J = 0 ∧ K ≥ 2)
  · exact entryConflict_impossible gc (phase_dispatch_ec gc (right i) phase hbL hbR hmech)
  · exact entryConflict_impossible gc
      (palindromic_phase_ec_residual gc (right i) hbL hbR phase hmech _hno_safe hn _hconv _hsub _h3bin_global)

private theorem consecutive_binary_isolated_false
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (_hconv : converges sys gc)
    (i : Fin sys.rs.n)
    (h3bin : threeConsecutiveBinary sys.rs i)
    (_hfc : gc.fireCount (right i) ≥ 2)
    (_hiso : ∀ (a : Fin gc.configs.length),
      gc.moverAt a = right i → gc.moverAt (nextIndex gc.configs a) ≠ right i)
    (_hsub : subThreshold sys.rs) (_h3bin_global : hasGe3Binary sys.rs)
    (hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0) : False := by
  by_cases hsafe : ∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q
  · obtain ⟨q, hq⟩ := hsafe
    exact small_arc_contradicts_convergence (by omega) gc _hconv q hq
  · by_cases hsubset : ∀ k : Fin gc.configs.length,
        gc.moverAt k = i ∨
        gc.moverAt k = right i ∨
        gc.moverAt k = right (right i)
    · obtain ⟨q, hq⟩ := safeProcessor_of_mover_subset_triple (by omega) gc i hsubset
      exact hsafe ⟨q, hq⟩
    · push_neg at hsubset
      exact consecutive_binary_isolated_false_noSafe_outsideMover
        hn gc _hconv i h3bin _hfc _hiso hsafe hsubset _hsub _h3bin_global hfull

/-- **Sweep sub-threshold contradiction.**

    Any sweep good cycle (|totalDisplacement| ≥ 2n) in a converging
    sub-threshold system with n ≥ 9 and ≥ 3 binary processors is impossible.

    **Proof**: isSweep forces |edgeNetFlow| ≥ 2 → every processor fires ≥ 2.
    For 3 consecutive binary: apply binary_isolated_firings_or_ec to the
    middle binary processor. EC and permanent cases close directly; isolated
    delegates to consecutive_binary_isolated_false (sorry-free).

    For non-consecutive binary: apply binary_isolated_firings_or_ec to any
    binary processor. EC and permanent cases close directly (sorry-free);
    isolated delegates to subThreshold_binary_core_false (bypasses
    nonConsecutive_phase_extraction_false, routes more directly to the
    binary_ring_impossibility via allNormalForm_false).

    Key steps:
    1. isSweep ⇒ |edgeNetFlow| ≥ 2 ⇒ fireCount ≥ 2 for ALL processors.
    2. binary_isolated_firings_or_ec: EC ∨ permanent ∨ isolated.
    3. Permanent mover ⇒ W = 0, contradicting isSweep.
    4. Isolated + consecutive ⇒ phase extraction entry conflict (sorry-free).
    5. Isolated + non-consecutive ⇒ subThreshold_binary_core_false. -/
private theorem sweep_sub_threshold_false
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (_hsub : subThreshold sys.rs) (h3bin : hasGe3Binary sys.rs)
    (hsweep : gc.isSweep) : False := by
  -- Step 1: Every processor fires ≥ 2 times.
  have hfc2 : ∀ p : Fin sys.rs.n, gc.fireCount p ≥ 2 :=
    sweep_fireCount_ge_two gc hsweep
  -- Step 2: Find 3 consecutive binary (or non-consecutive).
  -- Sub-threshold implies ≥ 3 binary.
  -- We case-split on whether 3 are consecutive.
  by_cases h3consec : ∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i
  · -- CONSECUTIVE CASE: 3 consecutive binary i, ri, rri
    obtain ⟨i, hbin_i, hbin_ri, hbin_rri⟩ := h3consec
    have h3bin_i : threeConsecutiveBinary sys.rs i := ⟨hbin_i, hbin_ri, hbin_rri⟩
    have hfc_ri := hfc2 (right i)
    rcases binary_isolated_firings_or_ec gc (right i) hbin_ri hfc_ri with hec | hperm | hiso
    · exact entryConflict_impossible gc hec
    · exfalso
      have hW0 := permanent_mover_totalDisplacement_zero gc (right i) hperm
      unfold GoodCycle.isSweep at hsweep
      have h0 : (totalDisplacement gc).natAbs = 0 := by rw [hW0]; decide
      omega
    · exact consecutive_binary_isolated_false hn gc hconv i h3bin_i hfc_ri hiso _hsub h3bin
        (fun p => by have := hfc2 p; omega)
  · -- NON-CONSECUTIVE CASE: use binary_isolated_firings_or_ec directly.
    -- Step 1: Get a binary processor from ≥ 3 non-consecutive binary.
    obtain ⟨p, _, hbin_p, _⟩ :=
      exists_binary_nonadjacent_pair_of_hasGe3Binary_noThreeConsecutive sys.rs h3bin h3consec
    -- Step 2: Sweep → fireCount ≥ 2 for p.
    have hfc_p := hfc2 p
    -- Step 3: Trichotomy — EC ∨ permanent ∨ isolated.
    rcases binary_isolated_firings_or_ec gc p hbin_p hfc_p with hec | hperm | hiso
    · -- Entry conflict → done (sorry-free).
      exact entryConflict_impossible gc hec
    · -- Permanent mover → totalDisplacement = 0, contradicting isSweep.
      exfalso
      have hW0 := permanent_mover_totalDisplacement_zero gc p hperm
      unfold GoodCycle.isSweep at hsweep
      have h0 : (totalDisplacement gc).natAbs = 0 := by rw [hW0]; decide
      omega
    · -- Isolated firings → MinFiringGap with gap ≥ 2.
      -- Route through subThreshold_binary_core_false (bypasses
      -- nonConsecutive_phase_extraction_false, hits binary_ring_impossibility
      -- more directly).
      have hno_safe_sweep : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
          gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q :=
        no_safeProcessor_of_nonZeroWinding gc (by
          intro hzero; unfold GoodCycle.zeroWinding at hzero
          unfold GoodCycle.isSweep at hsweep; omega)
      exact subThreshold_binary_core_false_residual gc hn _hsub h3bin hconv hno_safe_sweep

/-- **Odd-winding non-uniform sub-threshold contradiction.**

    Any odd-winding (|totalDisplacement| = n), non-uniform-direction good
    cycle in a converging sub-threshold system with n ≥ 9 and ≥ 3 binary
    processors is impossible.

    Mathematical proof: The flux lemma gives `edgeNetFlow p = ±1` (constant
    across all edges). Non-uniform direction means both CW and CCW steps exist.
    At any edge with ≥ 2 crossings (traversal count ≥ 3, since odd), both
    CW and CCW crossings occur. With ≥ 3 binary processors and no safe
    processor (forced by odd winding), a binary boundary edge has
    bidirectional crossings, yielding an entry conflict.

    The full 4-mechanism argument (Both-Even Return, Toggle-FR, Zero-Side EC,
    Traversal Return) + 2 ring-level lemmas (Parity Obstruction, Ring
    Alternation) covers all cases. Computationally verified for n=5,6,8
    with 0 exceptions. -/
private theorem oddWinding_nonUniform_sub_threshold_false
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (_hconv : converges sys gc)
    (_hsub : subThreshold sys.rs) (_h3bin : hasGe3Binary sys.rs)
    (_hodd : gc.isOddWinding) (_hnonunif : ¬gc.uniformDirection) : False := by
  -- Case split: 3 consecutive binary or not
  by_cases h3consec : ∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i
  · -- CONSECUTIVE CASE: 3 consecutive binary i, ri, rri
    obtain ⟨i, hbin_i, hbin_ri, hbin_rri⟩ := h3consec
    -- Step 1: ri = right i fires ≥ 1 under odd winding.
    -- Odd winding → edgeTraversalCount > 0 at every edge.
    -- Sum of two adjacent edge traversals = 2 * (fireCount - stayMoveCountAt).
    -- Both traversals > 0 → sum ≥ 2 → fireCount ≥ stayMoveCountAt + 1 ≥ 1.
    have hfc_pos : gc.fireCount (right i) > 0 := by
      have h1 := gc.edgeTraversalCount_pos_of_isOddWinding _hodd (left (right i))
      have h2 := gc.edgeTraversalCount_pos_of_isOddWinding _hodd (right i)
      have hsum := gc.edgeTraversalCount_left_add_edgeTraversalCount_eq_twice_fireCount_sub_stay (right i)
      omega
    -- Step 2: binary → even fireCount → fireCount ≥ 2
    have hfc_ri := binary_fireCount_ge_two gc (right i) hbin_ri hfc_pos
    -- Step 3: trichotomy — EC ∨ permanent ∨ isolated
    rcases binary_isolated_firings_or_ec gc (right i) hbin_ri hfc_ri with hec | hperm | hiso
    · -- Entry conflict → done
      exact entryConflict_impossible gc hec
    · -- Permanent mover → totalDisplacement = 0, contradicts odd winding (|W| = n ≥ 9)
      exfalso
      have hW0 := permanent_mover_totalDisplacement_zero gc (right i) hperm
      unfold GoodCycle.isOddWinding at _hodd
      have h0 : (totalDisplacement gc).natAbs = 0 := by rw [hW0]; decide
      omega
    · -- Isolated firings → shared helper with hfull derived from odd winding
      have hfull_odd : ∀ p : Fin sys.rs.n, gc.fireCount p > 0 := by
        intro p
        have h1 := gc.edgeTraversalCount_pos_of_isOddWinding _hodd (left p)
        have h2 := gc.edgeTraversalCount_pos_of_isOddWinding _hodd p
        have hsum := gc.edgeTraversalCount_left_add_edgeTraversalCount_eq_twice_fireCount_sub_stay p
        omega
      exact consecutive_binary_isolated_false hn gc _hconv i ⟨hbin_i, hbin_ri, hbin_rri⟩ hfc_ri hiso _hsub _h3bin
        hfull_odd
  · -- NON-CONSECUTIVE CASE: use binary_isolated_firings_or_ec directly
    -- (mirrors sweep non-consecutive pattern, bypasses nonConsecutive_phase_extraction_false).
    -- Step 1: Get a binary processor from ≥ 3 non-consecutive binary.
    obtain ⟨p, _, hbin_p, _⟩ :=
      exists_binary_nonadjacent_pair_of_hasGe3Binary_noThreeConsecutive sys.rs _h3bin h3consec
    -- Step 2: Odd winding → fireCount p > 0 → fireCount p ≥ 2 (binary).
    have hfc_pos : gc.fireCount p > 0 := by
      have h1 := gc.edgeTraversalCount_pos_of_isOddWinding _hodd (left p)
      have h2 := gc.edgeTraversalCount_pos_of_isOddWinding _hodd p
      have hsum := gc.edgeTraversalCount_left_add_edgeTraversalCount_eq_twice_fireCount_sub_stay p
      omega
    have hfc_p := binary_fireCount_ge_two gc p hbin_p hfc_pos
    -- Step 3: Trichotomy — EC ∨ permanent ∨ isolated.
    rcases binary_isolated_firings_or_ec gc p hbin_p hfc_p with hec | hperm | hiso
    · -- Entry conflict → done (sorry-free).
      exact entryConflict_impossible gc hec
    · -- Permanent mover → totalDisplacement = 0, contradicts odd winding.
      exfalso
      have hW0 := permanent_mover_totalDisplacement_zero gc p hperm
      unfold GoodCycle.isOddWinding at _hodd
      have h0 : (totalDisplacement gc).natAbs = 0 := by rw [hW0]; decide
      omega
    · -- Isolated firings → route through subThreshold_binary_core_false.
      have hno_safe_odd : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
          gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q :=
        no_safeProcessor_of_nonZeroWinding gc (by
          intro hzero; unfold GoodCycle.zeroWinding at hzero
          unfold GoodCycle.isOddWinding at _hodd; omega)
      exact subThreshold_binary_core_false_residual gc hn _hsub _h3bin _hconv hno_safe_odd

/-! ### Two sub-case theorems -/

/-- **Large-arc zero-winding obstruction (proved).**

    A zero-winding good cycle with cwStepCount > 0 and no safe processor
    (every processor is within distance 1 of some mover) in a converging
    sub-threshold system with n ≥ 9 is impossible.

    Proved via the global minimum-gap entry conflict argument:
    1. Sub-threshold → ≥ 3 binary processors.
    2. Zero winding + CW crossings → paired opposite-direction crossings.
    3. Global min gap → stay chain (all interior movers at boundary processor).
    4. Contiguous run of binary stay processor → entry conflict → False. -/
theorem large_arc_zeroWinding_ec
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (hzero : gc.zeroWinding)
    (hcw_pos : 0 < gc.cwStepCount)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q) :
    False := by
  exact subThreshold_binary_core_false_residual gc hn hsub
    (subThreshold_ge3_binary sys.rs hsub) hconv hno_safe

/-- **Non-zero-winding obstruction (proved).**

    Any non-zero-winding good cycle in a converging sub-threshold system
    with n ≥ 7 is impossible.

    Note: by `no_safeProcessor_of_nonZeroWinding`, no safe processor
    exists, so `small_arc_contradicts_convergence` does not apply.
    This case genuinely requires shadow cycle / entry conflict arguments.

    Proof by case split on cycle type:
    - Sweep (|W| ≥ 2n): `sweep_sub_threshold_false` (shadow cycle mirror theorem).
    - Odd winding (|W| = n), uniform: excluded by binary parity
      (`not_uniformDirection_and_isOddWinding_of_hasGe3Binary`).
    - Odd winding, non-uniform: `oddWinding_nonUniform_sub_threshold_false`
      (universal entry conflict, 4 mechanisms + 2 ring-level lemmas). -/
theorem nonZeroWinding_shadow
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (hnz : ¬gc.zeroWinding) :
    False := by
  have h3bin : hasGe3Binary sys.rs := subThreshold_ge3_binary sys.rs hsub
  by_cases hsweep : gc.isSweep
  · -- Sweep case: shadow cycle mirror theorem → ¬converges → contradiction
    exact sweep_sub_threshold_false hn gc hconv hsub h3bin hsweep
  · -- Non-sweep: must be zero winding or odd winding
    rcases gc.zeroWinding_or_isOddWinding_of_not_sweep hsweep with hzw | hodd
    · -- Zero winding: contradicts hypothesis ¬zeroWinding
      exact absurd hzw hnz
    · -- Odd winding: case split on uniform vs non-uniform direction
      by_cases hunif : gc.uniformDirection
      · -- Odd winding + uniform direction: excluded by binary parity
        exact absurd ⟨hunif, hodd⟩
          (gc.not_uniformDirection_and_isOddWinding_of_hasGe3Binary h3bin)
      · -- Odd winding + non-uniform direction: universal entry conflict
        exact oddWinding_nonUniform_sub_threshold_false hn gc hconv hsub h3bin hodd hunif

/-- **Sub-threshold obstruction (proved).**

    Any good cycle in a converging sub-threshold system with n ≥ 9 is
    impossible.  Proved by case-splitting on zero/non-zero winding, with
    the zero-winding case further split into all-stay, safe-processor,
    and large-arc sub-cases.

    Uses proved theorems:
    - `all_stay_contradicts_convergence`: cwStepCount = 0.
    - `small_arc_contradicts_convergence`: ∃ safe processor.
    - `large_arc_zeroWinding_ec`: zero winding, no safe proc.
    - `nonZeroWinding_shadow`: non-zero winding. -/
theorem subThreshold_obstruction
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) :
    False := by
  by_cases hzero : gc.zeroWinding
  · -- Zero winding: case split on cwStepCount and safe processor
    by_cases hcw : gc.cwStepCount = 0
    · exact all_stay_contradicts_convergence (by omega) gc hconv hzero hcw
    · by_cases hsafe : ∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
          gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q
      · obtain ⟨q, hq⟩ := hsafe
        exact small_arc_contradicts_convergence (by omega) gc hconv q hq
      · exact large_arc_zeroWinding_ec hn gc hconv hsub hzero (by omega) hsafe
  · -- Non-zero winding
    exact nonZeroWinding_shadow hn gc hconv hsub hzero

/-- **Large-arc zero-winding obstruction** (derived from `large_arc_zeroWinding_ec`). -/
theorem large_arc_zeroWinding_obstruction
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (hzero : gc.zeroWinding)
    (hcw_pos : 0 < gc.cwStepCount)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q) :
    False :=
  large_arc_zeroWinding_ec hn gc hconv hsub hzero hcw_pos hno_safe

/-- **Zero-winding obstruction (proved).** Any zero-winding good cycle in a
    converging sub-threshold system with n ≥ 9 is impossible.

    Case split:
    1. cwStepCount = 0 → `all_stay_contradicts_convergence`
    2. cwStepCount > 0, ∃ safe processor q → `small_arc_contradicts_convergence`
    3. cwStepCount > 0, no safe processor → `large_arc_zeroWinding_ec` -/
theorem zeroWinding_obstruction
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (hzero : gc.zeroWinding) :
    False := by
  by_cases hcw : gc.cwStepCount = 0
  · exact all_stay_contradicts_convergence (by omega) gc hconv hzero hcw
  · by_cases hsafe : ∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
        gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q
    · obtain ⟨q, hq⟩ := hsafe
      exact small_arc_contradicts_convergence (by omega) gc hconv q hq
    · exact large_arc_zeroWinding_ec hn gc hconv hsub hzero (by omega) hsafe

/-- **Non-zero-winding obstruction** (proved via `nonZeroWinding_shadow`). -/
theorem nonZeroWinding_obstruction
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (hnonzero : ¬gc.zeroWinding) :
    False :=
  nonZeroWinding_shadow hn gc hconv hsub hnonzero

/-- Sweep obstruction (proved): sweep cycles in converging sub-threshold
    systems with n ≥ 9 are impossible.  Derived from
    `nonZeroWinding_obstruction` since sweeps have |W| ≥ 2n > 0. -/
theorem sweep_obstruction
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (hsweep : gc.isSweep)
    (h3bin : hasGe3Binary sys.rs) :
    False := by
  apply nonZeroWinding_obstruction hn gc hconv hsub
  intro hzero
  -- zeroWinding means totalDisplacement = 0, but isSweep means |W| ≥ 2n ≥ 18
  unfold GoodCycle.zeroWinding at hzero
  unfold GoodCycle.isSweep at hsweep
  have h0 : (totalDisplacement gc).natAbs = 0 := by
    rw [hzero]; decide
  omega

/-- Odd-winding non-uniform obstruction (proved): derived from
    `nonZeroWinding_obstruction` since odd winding has |W| = n > 0. -/
theorem oddWinding_nonUniform_obstruction
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (hodd : gc.isOddWinding)
    (_hnonunif : ¬gc.uniformDirection) (h3bin : hasGe3Binary sys.rs) :
    False := by
  apply nonZeroWinding_obstruction hn gc hconv hsub
  intro hzero
  -- zeroWinding means totalDisplacement = 0, but isOddWinding means |W| = n ≥ 9
  unfold GoodCycle.zeroWinding at hzero
  unfold GoodCycle.isOddWinding at hodd
  have h0 : (totalDisplacement gc).natAbs = 0 := by
    rw [hzero]; decide
  omega

end LeanMn
