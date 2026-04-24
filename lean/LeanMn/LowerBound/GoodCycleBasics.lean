/-
  GoodCycleBasics.lean — Lower bound infrastructure (Phase 5)

  Defines: mover extraction, frontier count, local context,
  entry conflict, and the master obstruction lemma.
-/
import LeanMn.Dijkstra
import Mathlib.Algebra.BigOperators.ModEq

namespace LeanMn

variable {sys : System}

/-! ### Mover extraction from a good cycle -/

private theorem get_mem_configs (gc : GoodCycle sys) (k : Fin gc.configs.length) :
    gc.configs.get k ∈ gc.configs := by
  exact List.get_mem _ _

/-- The unique privileged processor at step k of a good cycle. -/
noncomputable def GoodCycle.moverAt (gc : GoodCycle sys) (k : Fin gc.configs.length) :
    Fin sys.rs.n :=
  (gc.unique_privileged (gc.configs.get k) (get_mem_configs gc k)).choose

/-- The mover at step k is privileged. -/
theorem GoodCycle.moverAt_privileged (gc : GoodCycle sys) (k : Fin gc.configs.length) :
    privileged sys (gc.configs.get k) (gc.moverAt k) :=
  ((gc.unique_privileged (gc.configs.get k) (get_mem_configs gc k)).choose_spec).1

/-- The mover at step k is the unique privileged processor. -/
theorem GoodCycle.moverAt_unique (gc : GoodCycle sys) (k : Fin gc.configs.length)
    (i : Fin sys.rs.n) (hi : privileged sys (gc.configs.get k) i) :
    i = gc.moverAt k :=
  ((gc.unique_privileged (gc.configs.get k) (get_mem_configs gc k)).choose_spec).2 i hi

/-- Any processor other than the mover is not privileged. -/
theorem GoodCycle.not_privileged_of_ne_moverAt (gc : GoodCycle sys)
    (k : Fin gc.configs.length) (i : Fin sys.rs.n) (hi : i ≠ gc.moverAt k) :
    ¬privileged sys (gc.configs.get k) i := by
  intro hpriv
  exact hi (gc.moverAt_unique k i hpriv)

/-- The mover word: list of processors that fire at each step. -/
noncomputable def GoodCycle.moverWord (gc : GoodCycle sys) : List (Fin sys.rs.n) :=
  (List.finRange gc.configs.length).map gc.moverAt

/-- The next configuration in a good cycle is obtained by firing `moverAt`. -/
theorem GoodCycle.step_eq_move (gc : GoodCycle sys) (k : Fin gc.configs.length) :
    gc.configs.get (nextIndex gc.configs k) = move sys (gc.configs.get k) (gc.moverAt k) := by
  obtain ⟨i, hpriv, hstep⟩ := gc.closed k
  have : i = gc.moverAt k := gc.moverAt_unique k i hpriv
  rw [this] at hstep
  exact hstep

/-- The value at any non-mover processor is unchanged across one good-cycle step. -/
theorem GoodCycle.state_eq_of_ne_moverAt (gc : GoodCycle sys)
    (k : Fin gc.configs.length) (i : Fin sys.rs.n) (hi : i ≠ gc.moverAt k) :
    (gc.configs.get (nextIndex gc.configs k)) i = (gc.configs.get k) i := by
  rw [gc.step_eq_move k]
  simp [move, hi]

/-- The mover's value changes across its step in the good cycle. -/
theorem GoodCycle.state_ne_at_moverAt (gc : GoodCycle sys) (k : Fin gc.configs.length) :
    (gc.configs.get (nextIndex gc.configs k)) (gc.moverAt k) ≠
      (gc.configs.get k) (gc.moverAt k) := by
  rw [gc.step_eq_move k]
  simpa [move] using gc.moverAt_privileged k

/-- A processor's value changes across a good-cycle step exactly when it is the mover. -/
theorem GoodCycle.state_ne_iff_moverAt (gc : GoodCycle sys)
    (k : Fin gc.configs.length) (i : Fin sys.rs.n) :
    (gc.configs.get (nextIndex gc.configs k)) i ≠ (gc.configs.get k) i ↔
      gc.moverAt k = i := by
  constructor
  · intro hne
    by_cases hi : i = gc.moverAt k
    · exact hi.symm
    · exfalso
      exact hne (gc.state_eq_of_ne_moverAt k i hi)
  · intro hi
    subst i
    exact gc.state_ne_at_moverAt k

/-- A processor's value is unchanged across a good-cycle step exactly when it is
    not the mover. -/
theorem GoodCycle.state_eq_iff_ne_moverAt (gc : GoodCycle sys)
    (k : Fin gc.configs.length) (i : Fin sys.rs.n) :
    (gc.configs.get (nextIndex gc.configs k)) i = (gc.configs.get k) i ↔
      i ≠ gc.moverAt k := by
  constructor
  · intro heq hi
    subst i
    exact gc.state_ne_at_moverAt k heq
  · intro hi
    exact gc.state_eq_of_ne_moverAt k i hi

/-- Indicator that processor `i` fires at step `k`. -/
noncomputable def GoodCycle.fireIndicator (gc : GoodCycle sys)
    (i : Fin sys.rs.n) (k : Nat) : Nat :=
  if hk : k < gc.configs.length then
    if gc.moverAt ⟨k, hk⟩ = i then 1 else 0
  else
    0

/-- Number of times processor `i` fires in the first `m` steps. -/
noncomputable def GoodCycle.prefixFireCount (gc : GoodCycle sys)
    (i : Fin sys.rs.n) (m : Nat) : Nat :=
  Finset.sum (Finset.range m) fun k => gc.fireIndicator i k

/-- Number of times processor `i` fires during one traversal of the good cycle. -/
noncomputable def GoodCycle.fireCount (gc : GoodCycle sys) (i : Fin sys.rs.n) : Nat :=
  gc.prefixFireCount i gc.configs.length

private theorem configs_length_pos' (gc : GoodCycle sys) : 0 < gc.configs.length := by
  cases h : gc.configs with
  | nil => exact (gc.nonempty h).elim
  | cons hd tl => simp

private def GoodCycle.firstIndex (gc : GoodCycle sys) : Fin gc.configs.length :=
  ⟨0, configs_length_pos' gc⟩

/-- State of processor `i` after `m` steps from the initial config.
    The full-cycle endpoint `m = length` wraps back to step `0`. -/
noncomputable def GoodCycle.stateAfter (gc : GoodCycle sys)
    (i : Fin sys.rs.n) (m : Nat) : Fin (sys.rs.m i) :=
  if hm : m < gc.configs.length then
    (gc.configs.get ⟨m, hm⟩) i
  else
    (gc.configs.get gc.firstIndex) i

@[simp] theorem GoodCycle.fireIndicator_of_lt (gc : GoodCycle sys)
    (i : Fin sys.rs.n) {k : Nat} (hk : k < gc.configs.length) :
    gc.fireIndicator i k = if gc.moverAt ⟨k, hk⟩ = i then 1 else 0 := by
  simp [GoodCycle.fireIndicator, hk]

@[simp] theorem GoodCycle.fireIndicator_of_ge (gc : GoodCycle sys)
    (i : Fin sys.rs.n) {k : Nat} (hk : gc.configs.length ≤ k) :
    gc.fireIndicator i k = 0 := by
  simp [GoodCycle.fireIndicator, Nat.not_lt.mpr hk]

@[simp] theorem GoodCycle.prefixFireCount_zero (gc : GoodCycle sys)
    (i : Fin sys.rs.n) :
    gc.prefixFireCount i 0 = 0 := by
  simp [GoodCycle.prefixFireCount]

@[simp] theorem GoodCycle.prefixFireCount_succ (gc : GoodCycle sys)
    (i : Fin sys.rs.n) (m : Nat) :
    gc.prefixFireCount i (m + 1) = gc.prefixFireCount i m + gc.fireIndicator i m := by
  rw [GoodCycle.prefixFireCount, GoodCycle.prefixFireCount, Finset.sum_range_succ]

@[simp] theorem GoodCycle.stateAfter_of_lt (gc : GoodCycle sys)
    (i : Fin sys.rs.n) {m : Nat} (hm : m < gc.configs.length) :
    gc.stateAfter i m = (gc.configs.get ⟨m, hm⟩) i := by
  simp [GoodCycle.stateAfter, hm]

@[simp] theorem GoodCycle.stateAfter_of_ge (gc : GoodCycle sys)
    (i : Fin sys.rs.n) {m : Nat} (hm : gc.configs.length ≤ m) :
    gc.stateAfter i m = (gc.configs.get gc.firstIndex) i := by
  simp [GoodCycle.stateAfter, Nat.not_lt.mpr hm]

theorem GoodCycle.stateAfter_succ_eq_next (gc : GoodCycle sys)
    (i : Fin sys.rs.n) {m : Nat} (hm : m < gc.configs.length) :
    gc.stateAfter i (m + 1) = (gc.configs.get (nextIndex gc.configs ⟨m, hm⟩)) i := by
  by_cases hm1 : m + 1 < gc.configs.length
  · simp [GoodCycle.stateAfter, hm1, nextIndex, Nat.mod_eq_of_lt hm1]
  · have hm1_eq : m + 1 = gc.configs.length := by omega
    simp [GoodCycle.stateAfter, nextIndex, hm1_eq, GoodCycle.firstIndex]

/-- stateAfter is constant when no fires occur in the interval.
    If processor q doesn't fire at any step in [a, b) where a ≤ b ≤ CL,
    then stateAfter q b = stateAfter q a. -/
theorem GoodCycle.stateAfter_eq_of_no_fire (gc : GoodCycle sys)
    (q : Fin sys.rs.n) {a b : Nat} (hab : a ≤ b) (hb : b ≤ gc.configs.length)
    (hno : ∀ k : Fin gc.configs.length, a ≤ k.val → k.val < b → gc.moverAt k ≠ q) :
    gc.stateAfter q b = gc.stateAfter q a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    have hb_lt : b < gc.configs.length := by omega
    have hno' : ∀ k : Fin gc.configs.length, a ≤ k.val → k.val < b → gc.moverAt k ≠ q :=
      fun k hk1 hk2 => hno k hk1 (by omega)
    have hih := ih (by omega) hno'
    have hfire : gc.moverAt ⟨b, hb_lt⟩ ≠ q :=
      hno ⟨b, hb_lt⟩ (by show a ≤ b; omega) (by show b < b + 1; omega)
    rw [gc.stateAfter_succ_eq_next q hb_lt,
        gc.state_eq_of_ne_moverAt ⟨b, hb_lt⟩ q (Ne.symm hfire),
        ← gc.stateAfter_of_lt q hb_lt, hih]

private lemma binary_flip_val {a b : Fin 2} (h : b ≠ a) :
    b.val = (a.val + 1) % 2 := by
  have ha : a.val < 2 := a.isLt
  have hb : b.val < 2 := b.isLt
  have hne : b.val ≠ a.val := by
    intro hval
    exact h (Fin.ext hval)
  omega

private theorem fireIndicator_le_one (gc : GoodCycle sys)
    (i : Fin sys.rs.n) (k : Nat) :
    gc.fireIndicator i k ≤ 1 := by
  unfold GoodCycle.fireIndicator
  split_ifs <;> omega

private theorem binary_stateAfter_succ_val (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hbin : sys.rs.m p = 2)
    {m : Nat} (hm : m < gc.configs.length) :
    (gc.stateAfter p (m + 1)).val =
      ((gc.stateAfter p m).val + gc.fireIndicator p m) % 2 := by
  let k : Fin gc.configs.length := ⟨m, hm⟩
  have hnext : gc.stateAfter p (m + 1) = (gc.configs.get (nextIndex gc.configs k)) p :=
    gc.stateAfter_succ_eq_next p hm
  have hcurr : gc.stateAfter p m = (gc.configs.get k) p := by
    simp [GoodCycle.stateAfter, hm, k]
  by_cases hmov : gc.moverAt k = p
  · have hne := gc.state_ne_at_moverAt k
    rw [hmov] at hne
    rw [hnext, hcurr, gc.fireIndicator_of_lt p hm]
    simp [k, hmov]
    set curr : Fin (sys.rs.m p) := (gc.configs.get k) p
    set next : Fin (sys.rs.m p) := (gc.configs.get (nextIndex gc.configs k)) p
    have hcurr_lt : curr.val < 2 := by
      simpa [curr, hbin] using curr.isLt
    have hnext_lt : next.val < 2 := by
      simpa [next, hbin] using next.isLt
    have hne_val : next.val ≠ curr.val := by
      intro hval
      exact hne (by
        apply Fin.ext
        simpa [curr, next] using hval)
    change next.val = (curr.val + 1) % 2
    omega
  · have heq : (gc.configs.get (nextIndex gc.configs k)) p = (gc.configs.get k) p := by
      exact gc.state_eq_of_ne_moverAt k p (by
        intro hp
        exact hmov hp.symm)
    have hfire : gc.fireIndicator p m = 0 := by
      rw [gc.fireIndicator_of_lt p hm]
      simp [k, hmov]
    rw [hnext, hcurr, hfire, heq]
    have hlt : ((gc.configs.get k) p).val < 2 := by
      simpa [hbin] using ((gc.configs.get k) p).isLt
    omega

/-- At a binary processor, the state after `m` steps is the initial value
    toggled by the parity of the first `m` firings. -/
theorem GoodCycle.binary_stateAfter_val_eq_initial_add_prefix (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hbin : sys.rs.m p = 2) :
    ∀ m : Nat, m ≤ gc.configs.length →
      (gc.stateAfter p m).val =
        (((gc.configs.get gc.firstIndex) p).val + gc.prefixFireCount p m) % 2
  | 0, _ => by
      rw [gc.stateAfter_of_lt p (configs_length_pos' gc), gc.prefixFireCount_zero]
      simp [GoodCycle.firstIndex]
      have hlt : ((gc.configs.get gc.firstIndex) p).val < 2 := by
        simpa [GoodCycle.firstIndex, hbin] using ((gc.configs.get gc.firstIndex) p).isLt
      omega
  | m + 1, hmle => by
      have hm : m < gc.configs.length := by omega
      have ih := gc.binary_stateAfter_val_eq_initial_add_prefix p hbin m (by omega)
      rw [binary_stateAfter_succ_val gc p hbin hm, ih, gc.prefixFireCount_succ]
      have hind : gc.fireIndicator p m ≤ 1 := fireIndicator_le_one gc p m
      omega

/-- Binary configuration values can be read off from prefix fire-count parity. -/
theorem GoodCycle.binary_config_val_eq_initial_add_prefix (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hbin : sys.rs.m p = 2) {m : Nat}
    (hm : m < gc.configs.length) :
    ((gc.configs.get ⟨m, hm⟩) p).val =
      (((gc.configs.get gc.firstIndex) p).val + gc.prefixFireCount p m) % 2 := by
  simpa [GoodCycle.stateAfter, hm] using
    gc.binary_stateAfter_val_eq_initial_add_prefix p hbin m (Nat.le_of_lt hm)

/-- Two times of a binary processor agree exactly when the intervening prefix
    fire counts have the same parity. -/
theorem GoodCycle.binary_stateAfter_eq_iff_prefixFireCount_modEq (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hbin : sys.rs.m p = 2) {a b : Nat}
    (ha : a ≤ gc.configs.length) (hb : b ≤ gc.configs.length) :
    gc.stateAfter p a = gc.stateAfter p b ↔
      gc.prefixFireCount p a % 2 = gc.prefixFireCount p b % 2 := by
  have hfa := gc.binary_stateAfter_val_eq_initial_add_prefix p hbin a ha
  have hfb := gc.binary_stateAfter_val_eq_initial_add_prefix p hbin b hb
  have hinit_lt : ((gc.configs.get gc.firstIndex) p).val < 2 := by
    simpa [GoodCycle.firstIndex, hbin] using ((gc.configs.get gc.firstIndex) p).isLt
  constructor
  · intro hEq
    have hEqVal : (gc.stateAfter p a).val = (gc.stateAfter p b).val := congrArg Fin.val hEq
    rw [hfa, hfb] at hEqVal
    omega
  · intro hpar
    apply Fin.ext
    rw [hfa, hfb]
    omega

/-- In particular, an even prefix fire count returns a binary processor to its
    initial value. -/
theorem GoodCycle.binary_stateAfter_eq_stateAfter_zero_of_prefixFireCount_even
    (gc : GoodCycle sys) (p : Fin sys.rs.n) (hbin : sys.rs.m p = 2) {m : Nat}
    (hm : m ≤ gc.configs.length) (heven : Even (gc.prefixFireCount p m)) :
    gc.stateAfter p m = gc.stateAfter p 0 := by
  refine (gc.binary_stateAfter_eq_iff_prefixFireCount_modEq p hbin hm (Nat.zero_le _)).2 ?_
  simpa [gc.prefixFireCount_zero] using Nat.even_iff.mp heven

/-- A binary processor fires an even number of times in any good cycle. -/
theorem GoodCycle.binary_fireCount_even_of_eq_two (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hbin : sys.rs.m p = 2) :
    Even (gc.fireCount p) := by
  have hformula := binary_stateAfter_val_eq_initial_add_prefix gc p hbin gc.configs.length le_rfl
  rw [gc.stateAfter_of_ge p (le_rfl : gc.configs.length ≤ gc.configs.length)] at hformula
  have hformula' :
      ((gc.configs.get gc.firstIndex) p).val =
        (((gc.configs.get gc.firstIndex) p).val + gc.fireCount p) % 2 := by
    simpa [GoodCycle.fireCount] using hformula
  have hstart_lt : ((gc.configs.get gc.firstIndex) p).val < 2 := by
    simpa [GoodCycle.firstIndex, hbin] using ((gc.configs.get gc.firstIndex) p).isLt
  have hmod : gc.fireCount p % 2 = 0 := by
    omega
  exact Nat.even_iff.mpr hmod

private lemma move_at_ne (c : Config sys.rs) (p q : Fin sys.rs.n)
    (hne : q ≠ p) : move sys c p q = c q := by
  simp [move, hne]

private lemma privileged_move_far_iff (c : Config sys.rs)
    (p q : Fin sys.rs.n)
    (hq : q ≠ p)
    (hl : left q ≠ p)
    (hr : right q ≠ p) :
    privileged sys (move sys c p) q ↔ privileged sys c q := by
  unfold privileged
  rw [move_at_ne c p q hq, move_at_ne c p (left q) hl, move_at_ne c p (right q) hr]

/-- After processor `p` fires, only `p` or one of its ring neighbors can become
    the next mover: every other processor sees the same local context as before
    the move, so it remains non-privileged. -/
theorem GoodCycle.next_mover_is_local (gc : GoodCycle sys) (k : Fin gc.configs.length) :
    let p := gc.moverAt k
    let k' := nextIndex gc.configs k
    gc.moverAt k' = left p ∨ gc.moverAt k' = p ∨ gc.moverAt k' = right p := by
  simp only []
  by_cases hleft : gc.moverAt (nextIndex gc.configs k) = left (gc.moverAt k)
  · exact Or.inl hleft
  · by_cases hself : gc.moverAt (nextIndex gc.configs k) = gc.moverAt k
    · exact Or.inr (Or.inl hself)
    · by_cases hright : gc.moverAt (nextIndex gc.configs k) = right (gc.moverAt k)
      · exact Or.inr (Or.inr hright)
      · exfalso
        set p := gc.moverAt k
        set k' := nextIndex gc.configs k
        set q := gc.moverAt k'
        have hq_ne : q ≠ p := by
          intro h
          exact hself (by simpa [p, q] using h)
        have hq_ne_left : q ≠ left p := by
          intro h
          exact hleft (by simpa [p, q] using h)
        have hq_ne_right : q ≠ right p := by
          intro h
          exact hright (by simpa [p, q] using h)
        have hleftq_ne_p : left q ≠ p := by
          intro h
          have : q = right p := by
            calc
              q = right (left q) := by symm; simpa using (right_left_eq_self q)
              _ = right p := by rw [h]
          exact hq_ne_right this
        have hrightq_ne_p : right q ≠ p := by
          intro h
          have : q = left p := by
            calc
              q = left (right q) := by symm; simpa using (left_right_eq_self q)
              _ = left p := by rw [h]
          exact hq_ne_left this
        have hstep := gc.closed k
        obtain ⟨i, hpriv_i, hmove⟩ := hstep
        have hi : i = p := gc.moverAt_unique k i hpriv_i
        rw [hi] at hmove
        have hq_priv_next : privileged sys (gc.configs.get k') q :=
          gc.moverAt_privileged k'
        have hq_priv_now : privileged sys (gc.configs.get k) q := by
          have hiff := privileged_move_far_iff (sys := sys) (c := gc.configs.get k)
            p q hq_ne hleftq_ne_p hrightq_ne_p
          rw [hmove] at hq_priv_next
          exact hiff.mp hq_priv_next
        exact hq_ne (gc.moverAt_unique k q hq_priv_now)

/-! ### Frontier count -/

/-- Frontier count: number of adjacent processor pairs with different state values.
    Compares `.val` because adjacent processors may have different state space sizes. -/
def fc (rs : RingSpec) (c : Config rs) : Nat :=
  (Finset.univ.filter (fun i : Fin rs.n => (c i).val ≠ (c (right i)).val)).card

/-! ### Entry conflict -/

/-- An entry conflict at processor i between steps k₁ (mover) and k₂ (non-mover):
    the same local context (L, S, R) appears at both a mover step and a non-mover step.
    This is impossible because f_i(L,S,R) must simultaneously equal S and not equal S. -/
def hasEntryConflict (gc : GoodCycle sys) : Prop :=
  ∃ (k₁ k₂ : Fin gc.configs.length) (i : Fin sys.rs.n),
    -- i is the mover at step k₁
    gc.moverAt k₁ = i ∧
    -- i is NOT the mover at step k₂
    gc.moverAt k₂ ≠ i ∧
    -- Same local context (L, S, R) at processor i
    (gc.configs.get k₁) (left i) = (gc.configs.get k₂) (left i) ∧
    (gc.configs.get k₁) i = (gc.configs.get k₂) i ∧
    (gc.configs.get k₁) (right i) = (gc.configs.get k₂) (right i)

/-- Master obstruction: an entry conflict is impossible in any good cycle.
    If the same (L, S, R) context appears at processor i at both a mover step
    (where f_i(L,S,R) ≠ S) and a non-mover step (where f_i(L,S,R) = S),
    the transition function would need to both equal and not equal S. -/
theorem entryConflict_impossible (gc : GoodCycle sys) (h : hasEntryConflict gc) : False := by
  obtain ⟨k₁, k₂, i, hmover, hnonmover, hL, hS, hR⟩ := h
  -- At k₁: i is the mover, so f_i(L₁, S₁, R₁) ≠ S₁
  have hpriv : privileged sys (gc.configs.get k₁) i := by
    rw [← hmover]; exact gc.moverAt_privileged k₁
  -- At k₂: i is not the mover, so ¬privileged, i.e., f_i(L₂, S₂, R₂) = S₂
  have hnotpriv : ¬privileged sys (gc.configs.get k₂) i :=
    gc.not_privileged_of_ne_moverAt k₂ i (Ne.symm hnonmover)
  -- privileged means f(L,S,R) ≠ S; not privileged means f(L,S,R) = S
  unfold privileged at hpriv hnotpriv
  push_neg at hnotpriv
  -- Rewrite using context equality
  rw [hL, hS, hR] at hpriv
  exact hpriv hnotpriv

/-! ### Signed step direction (for winding number) -/

/-- Direction of a step on the ring: +1 for CW, -1 for CCW, 0 for stay.
    CW means b = (a + 1) mod n; CCW means a = (b + 1) mod n. -/
def signedStep (n : Nat) (a b : Fin n) : Int :=
  if (a.val + 1) % n = b.val then 1
  else if (b.val + 1) % n = a.val then -1
  else 0

private lemma right_ne_self_local {n : Nat} (hn : 4 ≤ n) (a : Fin n) :
    right a ≠ a := by
  intro h
  exact absurd (congrArg Fin.val h) (by
    simp only [right_val]
    have ha := a.isLt
    by_cases hp1 : a.val + 1 < n
    · rw [Nat.mod_eq_of_lt hp1]
      omega
    · rw [show a.val + 1 = n from by omega, Nat.mod_self]
      omega)

private lemma right_ne_left_local {n : Nat} (hn : 4 ≤ n) (a : Fin n) :
    right a ≠ left a := by
  intro h
  exact absurd (congrArg Fin.val h) (by
    simp only [right_val, left_val]
    have ha := a.isLt
    by_cases h0 : a.val = 0
    · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · by_cases hlast : a.val + 1 < n
      · rw [Nat.mod_eq_of_lt hlast]
        rw [show a.val + n - 1 = (a.val - 1) + n from by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
        omega
      · have hwrap : a.val + 1 = n := by omega
        rw [hwrap, Nat.mod_self]
        rw [show a.val + n - 1 = (a.val - 1) + n from by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
        omega)

@[simp] theorem signedStep_right {n : Nat} (a : Fin n) :
    signedStep n a (right a) = 1 := by
  unfold signedStep
  simp [right_val]

@[simp] theorem signedStep_self {n : Nat} (hn : 4 ≤ n) (a : Fin n) :
    signedStep n a a = 0 := by
  unfold signedStep
  have h1 : (a.val + 1) % n ≠ a.val := by
    intro h
    exact right_ne_self_local hn a (Fin.ext h)
  simp [h1]

private lemma left_step_mod {n : Nat} (hn : 4 ≤ n) (a : Fin n) :
    ((a.val + n - 1) % n + 1) % n = a.val := by
  by_cases h0 : a.val = 0
  · rw [h0, Nat.zero_add]
    nth_rewrite 1 [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    rw [show n - 1 + 1 = n from by omega, Nat.mod_self]
  · nth_rewrite 1 [show (a.val + n - 1) % n = a.val - 1 by
      rw [show a.val + n - 1 = (a.val - 1) + n from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
    rw [show a.val - 1 + 1 = a.val from by omega, Nat.mod_eq_of_lt a.isLt]

@[simp] theorem signedStep_left {n : Nat} (hn : 4 ≤ n) (a : Fin n) :
    signedStep n a (left a) = -1 := by
  unfold signedStep
  rw [left_val]
  have h1 : (a.val + 1) % n ≠ (a.val + n - 1) % n := by
    intro h
    exact right_ne_left_local hn a (Fin.ext (by simpa [right_val, left_val] using h))
  have h2 : ((a.val + n - 1) % n + 1) % n = a.val := left_step_mod hn a
  simp [h1, h2]

/-- The mover word has the same length as the config list. -/
theorem GoodCycle.moverWord_length (gc : GoodCycle sys) :
    gc.moverWord.length = gc.configs.length := by
  simp [GoodCycle.moverWord]

/-- The config list is nonempty, so its length is positive. -/
theorem GoodCycle.configs_length_pos (gc : GoodCycle sys) : 0 < gc.configs.length := by
  cases h : gc.configs with
  | nil => exact absurd h gc.nonempty
  | cons hd tl => simp

lemma nextIndex_eq_right {α : Type} (xs : List α) (k : Fin xs.length) :
    nextIndex xs k = right k := by
  ext
  simp [nextIndex, right]

lemma nextIndex_bijective {α : Type} (xs : List α) :
    Function.Bijective (nextIndex xs) := by
  constructor
  · intro a b hab
    have ha : left (nextIndex xs a) = a := by
      simpa [nextIndex_eq_right] using (left_right_eq_self a)
    have hb : left (nextIndex xs b) = b := by
      simpa [nextIndex_eq_right] using (left_right_eq_self b)
    calc
      a = left (nextIndex xs a) := ha.symm
      _ = left (nextIndex xs b) := by rw [hab]
      _ = b := hb
  · intro b
    refine ⟨left b, ?_⟩
    simpa [nextIndex_eq_right] using (right_left_eq_self b)

/-- Total signed displacement of a closed walk (mover word) on C_n. -/
noncomputable def totalDisplacement (gc : GoodCycle sys) : Int :=
  ∑ k : Fin gc.configs.length,
    let w := gc.moverWord
    let curr := w.get ⟨k.val, by rw [gc.moverWord_length]; exact k.isLt⟩
    let next := w.get ⟨(k.val + 1) % w.length, by
      rw [gc.moverWord_length]; exact Nat.mod_lt _ gc.configs_length_pos⟩
    signedStep sys.rs.n curr next

lemma totalDisplacement_eq_moverAt_sum (gc : GoodCycle sys) :
    totalDisplacement gc =
      ∑ k : Fin gc.configs.length,
        signedStep sys.rs.n (gc.moverAt k) (gc.moverAt (nextIndex gc.configs k)) := by
  unfold totalDisplacement GoodCycle.moverWord
  simp_rw [← List.ofFn_eq_map]
  apply Finset.sum_congr rfl
  intro k
  simp [nextIndex]

private lemma signedStep_modEq_sub (gc : GoodCycle sys) (k : Fin gc.configs.length) :
    signedStep sys.rs.n (gc.moverAt k) (gc.moverAt (nextIndex gc.configs k)) ≡
      (((gc.moverAt (nextIndex gc.configs k)).val : Int) - (gc.moverAt k).val)
        [ZMOD (sys.rs.n : Int)] := by
  rcases gc.next_mover_is_local k with hleft | hself | hright
  · rw [hleft]
    rw [signedStep_left sys.rs.n_ge_4]
    rw [Int.modEq_iff_dvd]
    by_cases h0 : (gc.moverAt k).val = 0
    · simp [left_val, h0]
      refine ⟨1, ?_⟩
      omega
    · have hleftval : (left (gc.moverAt k)).val = (gc.moverAt k).val - 1 := by
        rw [left_val,
          show (gc.moverAt k).val + sys.rs.n - 1 = ((gc.moverAt k).val - 1) + sys.rs.n from by
            omega,
          Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hleftval]
      refine ⟨0, ?_⟩
      omega
  · rw [hself]
    rw [signedStep_self sys.rs.n_ge_4]
    simp
  · rw [hright]
    rw [signedStep_right]
    rw [Int.modEq_iff_dvd]
    by_cases htop : (gc.moverAt k).val + 1 < sys.rs.n
    · have hrightval : (right (gc.moverAt k)).val = (gc.moverAt k).val + 1 := by
        rw [right_val, Nat.mod_eq_of_lt htop]
      rw [hrightval]
      refine ⟨0, ?_⟩
      omega
    · have hlast : (gc.moverAt k).val + 1 = sys.rs.n := by omega
      have hrightval : (right (gc.moverAt k)).val = 0 := by
        simp [right_val, hlast]
      rw [hrightval]
      refine ⟨-1, ?_⟩
      omega

lemma sum_next_moverAt_val_eq_sum_moverAt_val (gc : GoodCycle sys) :
    (∑ k : Fin gc.configs.length, ((gc.moverAt (nextIndex gc.configs k)).val : Int)) =
      ∑ k : Fin gc.configs.length, ((gc.moverAt k).val : Int) := by
  simpa using
    (Fintype.sum_bijective (nextIndex gc.configs) (nextIndex_bijective gc.configs)
      (fun k => ((gc.moverAt (nextIndex gc.configs k)).val : Int))
      (fun k => ((gc.moverAt k).val : Int))
      (fun k => rfl))

/-- The total mover-word displacement of a good cycle is always divisible by `n`. -/
theorem GoodCycle.totalDisplacement_modEq_zero (gc : GoodCycle sys) :
    totalDisplacement gc ≡ 0 [ZMOD (sys.rs.n : Int)] := by
  rw [totalDisplacement_eq_moverAt_sum]
  have hsum :
      (∑ k : Fin gc.configs.length,
          signedStep sys.rs.n (gc.moverAt k) (gc.moverAt (nextIndex gc.configs k))) ≡
        (∑ k : Fin gc.configs.length,
          (((gc.moverAt (nextIndex gc.configs k)).val : Int) - (gc.moverAt k).val))
          [ZMOD (sys.rs.n : Int)] := by
    simpa using Int.ModEq.sum (s := Finset.univ) (fun k _ => signedStep_modEq_sub gc k)
  have htel :
      (∑ k : Fin gc.configs.length,
          (((gc.moverAt (nextIndex gc.configs k)).val : Int) - (gc.moverAt k).val)) = 0 := by
    rw [Finset.sum_sub_distrib, sum_next_moverAt_val_eq_sum_moverAt_val, sub_self]
  have hzero :
      (∑ k : Fin gc.configs.length,
          (((gc.moverAt (nextIndex gc.configs k)).val : Int) - (gc.moverAt k).val)) ≡
        0 [ZMOD (sys.rs.n : Int)] := by
    simpa [htel] using (Int.ModEq.refl (0 : Int))
  exact hsum.trans hzero

/-- Consecutive movers in a good cycle contribute exactly one of the three
    local step values `1`, `0`, or `-1` to the winding sum. -/
theorem GoodCycle.next_signedStep_cases (gc : GoodCycle sys)
    (k : Fin gc.configs.length) :
    let curr := gc.moverAt k
    let nxt := gc.moverAt (nextIndex gc.configs k)
    signedStep sys.rs.n curr nxt = 1 ∨
      signedStep sys.rs.n curr nxt = 0 ∨
      signedStep sys.rs.n curr nxt = -1 := by
  simp only []
  rcases gc.next_mover_is_local k with hleft | hself | hright
  · right
    right
    simpa [hleft] using signedStep_left sys.rs.n_ge_4 (gc.moverAt k)
  · right
    left
    simpa [hself] using signedStep_self sys.rs.n_ge_4 (gc.moverAt k)
  · left
    simpa [hright] using signedStep_right (gc.moverAt k)

/-! ### Cycle type classification -/

/-- A good cycle is a sweep if its total displacement has |W| ≥ 2n. -/
noncomputable def GoodCycle.isSweep (gc : GoodCycle sys) : Prop :=
  (totalDisplacement gc).natAbs ≥ 2 * sys.rs.n

/-- A good cycle has zero winding. -/
noncomputable def GoodCycle.zeroWinding (gc : GoodCycle sys) : Prop :=
  totalDisplacement gc = 0

/-- A good cycle has odd winding if |W| = n. -/
noncomputable def GoodCycle.isOddWinding (gc : GoodCycle sys) : Prop :=
  (totalDisplacement gc).natAbs = sys.rs.n

/-- Any non-sweep good cycle has either zero winding or odd winding. -/
theorem GoodCycle.zeroWinding_or_isOddWinding_of_not_sweep (gc : GoodCycle sys)
    (hnsweep : ¬gc.isSweep) :
    gc.zeroWinding ∨ gc.isOddWinding := by
  unfold GoodCycle.isSweep at hnsweep
  rcases Int.modEq_zero_iff_dvd.mp (gc.totalDisplacement_modEq_zero) with ⟨t, ht⟩
  have hlt : (totalDisplacement gc).natAbs < 2 * sys.rs.n := by
    omega
  have habs : (totalDisplacement gc).natAbs = sys.rs.n * Int.natAbs t := by
    rw [ht, Int.natAbs_mul]
    simp
  have htlt : Int.natAbs t < 2 := by
    by_contra hge
    have hge' : 2 ≤ Int.natAbs t := by omega
    rw [habs] at hlt
    have hmul : sys.rs.n * 2 ≤ sys.rs.n * Int.natAbs t := Nat.mul_le_mul_left _ hge'
    have hmul' : 2 * sys.rs.n ≤ sys.rs.n * Int.natAbs t := by
      simpa [Nat.mul_comm] using hmul
    omega
  have hcases : Int.natAbs t = 0 ∨ Int.natAbs t = 1 := by
    omega
  rcases hcases with hzero | hodd
  · left
    unfold GoodCycle.zeroWinding
    have ht0 : t = 0 := Int.natAbs_eq_zero.mp hzero
    rw [ht, ht0]
    simp
  · right
    unfold GoodCycle.isOddWinding
    rw [habs, hodd]
    simp

/-! ### Binary processor predicates -/

/-- Processor i is binary (has exactly 2 states). -/
def isBinary (rs : RingSpec) (i : Fin rs.n) : Prop := rs.m i = 2

/-- Processor i is ternary (has exactly 3 states). -/
def isTernary (rs : RingSpec) (i : Fin rs.n) : Prop := rs.m i = 3

/-- A binary processor fires an even number of times in any good cycle. -/
theorem GoodCycle.binary_fireCount_even (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hbin : isBinary sys.rs p) :
    Even (gc.fireCount p) :=
  gc.binary_fireCount_even_of_eq_two p hbin

/-- At each step, exactly one processor fires: the sum of fire indicators = 1. -/
theorem GoodCycle.sum_fireIndicator_eq_one (gc : GoodCycle sys)
    {k : Nat} (hk : k < gc.configs.length) :
    (∑ p : Fin sys.rs.n, gc.fireIndicator p k) = 1 := by
  classical
  let mover := gc.moverAt ⟨k, hk⟩
  rw [Finset.sum_eq_single mover]
  · rw [gc.fireIndicator_of_lt mover hk]
    simp [mover]
  · intro p hp hpne
    rw [gc.fireIndicator_of_lt p hk]
    simp [show gc.moverAt ⟨k, hk⟩ ≠ p from fun h => hpne h.symm]
  · intro hmover
    simpa [mover] using hmover

/-- Summing all processor fire counts recovers the cycle length:
    exactly one processor fires at each step. -/
theorem GoodCycle.sum_fireCount (gc : GoodCycle sys) :
    (∑ p : Fin sys.rs.n, gc.fireCount p) = gc.configs.length := by
  classical
  unfold GoodCycle.fireCount GoodCycle.prefixFireCount
  rw [Finset.sum_comm]
  calc
    Finset.sum (Finset.range gc.configs.length) (fun k => ∑ p : Fin sys.rs.n, gc.fireIndicator p k)
        = Finset.sum (Finset.range gc.configs.length) (fun _ => 1) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact gc.sum_fireIndicator_eq_one (Finset.mem_range.mp hk)
    _ = gc.configs.length := by simp

/-- Count of binary processors. -/
def binaryCount (rs : RingSpec) : Nat :=
  (Finset.univ.filter (fun i : Fin rs.n => rs.m i = 2)).card

/-- Three consecutive binary processors starting at position i. -/
def threeConsecutiveBinary (rs : RingSpec) (i : Fin rs.n) : Prop :=
  isBinary rs i ∧ isBinary rs (right i) ∧ isBinary rs (right (right i))

/-- The state vector has ≥ 3 binary processors. -/
def hasGe3Binary (rs : RingSpec) : Prop := binaryCount rs ≥ 3

/-- The state vector is sub-threshold: product < 4 · 3^(n-2). -/
def subThreshold (rs : RingSpec) : Prop :=
  stateProduct rs < 4 * 3 ^ (rs.n - 2)

/-! ### Ring topology helpers -/

section RingTopologyHelpers

variable {rs : RingSpec}

private theorem left_ne_self_local' (t : Fin rs.n) : left t ≠ t := by
  intro h
  have hrt : right t = t := by
    calc
      right t = right (left t) := by rw [h]
      _ = t := by simp
  exact right_ne_self_local rs.n_ge_4 t hrt

/-- left is injective on Fin n for n ≥ 1. -/
theorem left_injective (_hn : rs.n ≥ 1) (a b : Fin rs.n) (h : left a = left b) : a = b := by
  have hright := congrArg right h
  simpa using hright

/-- right is injective on Fin n for n ≥ 1. -/
theorem right_injective (_hn : rs.n ≥ 1) (a b : Fin rs.n) (h : right a = right b) : a = b := by
  have hleft := congrArg left h
  simpa using hleft

/-- left a ≠ left b when a ≠ b and n ≥ 1. -/
theorem left_ne_left (hn : rs.n ≥ 1) (a b : Fin rs.n) (hab : a ≠ b) : left a ≠ left b := by
  intro h
  exact hab (left_injective hn a b h)

/-- For n ≥ 3: left (left t) ≠ left t. -/
theorem left2_ne_left1 (hn : rs.n ≥ 3) (t : Fin rs.n) : left (left t) ≠ left t := by
  intro h
  have hlt : left t = t := left_injective (by omega) (left t) t h
  exact left_ne_self_local' t hlt

/-- `right q = left t` forces `q = left (left t)`, so it is impossible when
    `q ≠ left (left t)`. -/
theorem right_ne_left_of_ne (_hn : rs.n ≥ 3) (q t : Fin rs.n)
    (hqt : q ≠ left (left t)) : right q ≠ left t := by
  intro h
  apply hqt
  have hleft := congrArg left h
  simpa using hleft

end RingTopologyHelpers

end LeanMn
