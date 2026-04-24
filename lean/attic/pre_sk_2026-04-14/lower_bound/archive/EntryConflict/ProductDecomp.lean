/-
  ProductDecomp.lean — Product decomposition for the phase-shift proof

  Key lemma: between firings of a processor p, left and right halves of
  the ring evolve independently.  More precisely, if two configs agree
  on all positions except possibly a set S, and the mover is "far" from
  every position in S (i.e., the mover is not in S, not left of any
  element of S, not right of any element of S), then after the move the
  resulting configs still agree away from S.

  Main results (all sorry-free):
  1. `move_preserves_agreement`: two configs agreeing away from S still
     agree away from S after a move whose mover is far from S.
  2. `move_same_at_mover_of_local_agree`: the mover's new value depends
     only on the 3 local positions.
  3. `privileged_iff_of_local_eq`: privileged status depends only on
     the 3 local positions.
  4. `parallel_move_preserves_agreement`: parallel orbit engine for
     shadow-config construction.
  5. `parallel_orbit_privileged`: privileged status transfers to
     parallel configs.
-/
import LeanMn.LowerBound.EntryConflict.NestedFirings

namespace LeanMn

variable {sys : System}

/-! ### Core: move preserves pointwise agreement at far positions -/

/-- If two configs agree at position j, and j ≠ mover, then after the
    move they still agree at j.  This is the pointwise version. -/
theorem move_preserves_val_at_ne (c₁ c₂ : Config sys.rs)
    (mover : Fin sys.rs.n) (j : Fin sys.rs.n) (hj : j ≠ mover)
    (hagree : c₁ j = c₂ j) :
    (move sys c₁ mover) j = (move sys c₂ mover) j := by
  simp [move, hj, hagree]

/-- If two configs agree at left(mover), mover, and right(mover), then
    the move produces the same new value at the mover position. -/
theorem move_same_at_mover_of_local_agree (c₁ c₂ : Config sys.rs)
    (mover : Fin sys.rs.n)
    (hL : c₁ (left mover) = c₂ (left mover))
    (hS : c₁ mover = c₂ mover)
    (hR : c₁ (right mover) = c₂ (right mover)) :
    (move sys c₁ mover) mover = (move sys c₂ mover) mover := by
  simp [move, hL, hS, hR]

/-! ### Agreement predicate: two configs agree on a set of positions -/

/-- Two configs agree on all positions satisfying a predicate. -/
def AgreeOn (c₁ c₂ : Config sys.rs) (P : Fin sys.rs.n → Prop) : Prop :=
  ∀ j, P j → c₁ j = c₂ j

theorem AgreeOn.symm {c₁ c₂ : Config sys.rs} {P : Fin sys.rs.n → Prop}
    (h : AgreeOn c₁ c₂ P) : AgreeOn c₂ c₁ P :=
  fun j hj => (h j hj).symm

theorem AgreeOn.at_pos {c₁ c₂ : Config sys.rs} {P : Fin sys.rs.n → Prop}
    (h : AgreeOn c₁ c₂ P) {j : Fin sys.rs.n} (hj : P j) : c₁ j = c₂ j :=
  h j hj

/-- A position is "far" from the mover: not the mover, not left, not right. -/
def FarFrom (mover j : Fin sys.rs.n) : Prop :=
  j ≠ mover ∧ j ≠ left mover ∧ j ≠ right mover

/-! ### Product decomposition: move preserves agreement away from a set -/

/-- **Product decomposition (single step).**

    If two configs agree at all positions j where `P j` holds, and
    P j implies j ≠ mover, then after the move they still agree on P.

    This is the fundamental independence property: positions far from the
    mover are completely unaffected by the move. -/
theorem move_preserves_agreement (c₁ c₂ : Config sys.rs)
    (mover : Fin sys.rs.n) (P : Fin sys.rs.n → Prop)
    (hagree : AgreeOn c₁ c₂ P)
    (hmover_far : ∀ j, P j → j ≠ mover) :
    AgreeOn (move sys c₁ mover) (move sys c₂ mover) P := by
  intro j hj
  have hjm := hmover_far j hj
  simp [move, hjm, hagree j hj]

/-- **Complement agreement**: if two configs agree everywhere except
    possibly S, and the mover is in S, then after the move they still
    agree everywhere except possibly S. -/
theorem move_preserves_complement_agreement (c₁ c₂ : Config sys.rs)
    (mover : Fin sys.rs.n) (S : Fin sys.rs.n → Prop)
    (hagree : AgreeOn c₁ c₂ (fun j => ¬S j))
    (hmover_in_S : S mover) :
    AgreeOn (move sys c₁ mover) (move sys c₂ mover) (fun j => ¬S j) := by
  intro j hj
  have hjm : j ≠ mover := fun h => hj (h ▸ hmover_in_S)
  simp [move, hjm, hagree j hj]

/-! ### Multi-step product decomposition via good cycles -/

/-- If at good-cycle step k the mover is not p, then the value at p is
    unchanged.  (Re-export for convenience.) -/
theorem gc_val_unchanged_at_ne_mover (gc : GoodCycle sys)
    (k : Fin gc.configs.length) (p : Fin sys.rs.n)
    (hne : gc.moverAt k ≠ p) :
    (gc.configs.get (nextIndex gc.configs k)) p =
      (gc.configs.get k) p :=
  gc.state_eq_of_ne_moverAt k p (Ne.symm hne)

/-- **Key corollary**: if a processor p does not fire during steps a..b-1
    (where b < configs.length), then p's config value is the same at
    steps a and b. -/
theorem gc_config_const_if_no_fire (gc : GoodCycle sys)
    (p : Fin sys.rs.n)
    {a b : Nat} (hab : a ≤ b) (hb : b < gc.configs.length) (ha : a < gc.configs.length)
    (hno : ∀ (k : Nat) (hk : k < gc.configs.length), a ≤ k → k < b → gc.moverAt ⟨k, hk⟩ ≠ p) :
    (gc.configs.get ⟨b, hb⟩) p = (gc.configs.get ⟨a, ha⟩) p := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this; rfl
  | succ b ih =>
    by_cases hab' : a = b + 1
    · subst hab'; rfl
    · have hb' : b < gc.configs.length := by omega
      have hmov_ne : gc.moverAt ⟨b, hb'⟩ ≠ p := hno b hb' (by omega) (by omega)
      have hnext : (⟨b + 1, hb⟩ : Fin gc.configs.length) =
          nextIndex gc.configs ⟨b, hb'⟩ :=
        Fin.ext (by simp [nextIndex, Nat.mod_eq_of_lt (show b + 1 < gc.configs.length from hb)])
      rw [hnext, gc.state_eq_of_ne_moverAt ⟨b, hb'⟩ p (Ne.symm hmov_ne)]
      exact ih (by omega) hb' (fun k hk hak hkb => hno k hk hak (by omega))

/-! ### Shadow config construction from local agreement -/

/-- **Move result locality**: the result of `move sys c mover` at the
    mover position depends only on c at {left mover, mover, right mover}.
    Two configs with the same local triple produce the same new value. -/
theorem move_at_mover_eq_of_local_eq (c₁ c₂ : Config sys.rs)
    (mover : Fin sys.rs.n)
    (hL : c₁ (left mover) = c₂ (left mover))
    (hS : c₁ mover = c₂ mover)
    (hR : c₁ (right mover) = c₂ (right mover)) :
    (move sys c₁ mover) mover = (move sys c₂ mover) mover := by
  simp [move, hL, hS, hR]

/-- **Privileged locality**: whether processor i is privileged depends
    only on the values at {left i, i, right i}. -/
theorem privileged_iff_of_local_eq (c₁ c₂ : Config sys.rs)
    (i : Fin sys.rs.n)
    (hL : c₁ (left i) = c₂ (left i))
    (hS : c₁ i = c₂ i)
    (hR : c₁ (right i) = c₂ (right i)) :
    privileged sys c₁ i ↔ privileged sys c₂ i := by
  unfold privileged
  rw [hL, hS, hR]

/-- If two configs agree on {left i, i, right i} and one is privileged
    at i, so is the other. -/
theorem privileged_of_local_eq (c₁ c₂ : Config sys.rs)
    (i : Fin sys.rs.n)
    (hL : c₁ (left i) = c₂ (left i))
    (hS : c₁ i = c₂ i)
    (hR : c₁ (right i) = c₂ (right i))
    (hpriv : privileged sys c₁ i) :
    privileged sys c₂ i :=
  (privileged_iff_of_local_eq c₁ c₂ i hL hS hR).mp hpriv

/-- If two configs agree on {left i, i, right i} and one is NOT privileged
    at i, neither is the other. -/
theorem not_privileged_of_local_eq (c₁ c₂ : Config sys.rs)
    (i : Fin sys.rs.n)
    (hL : c₁ (left i) = c₂ (left i))
    (hS : c₁ i = c₂ i)
    (hR : c₁ (right i) = c₂ (right i))
    (hnotpriv : ¬privileged sys c₁ i) :
    ¬privileged sys c₂ i :=
  fun h => hnotpriv ((privileged_iff_of_local_eq c₁ c₂ i hL hS hR).mpr h)

/-! ### Ring topology helpers -/

private theorem left_ne_self_pd (p : Fin sys.rs.n) : left p ≠ p := by
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

private theorem right_ne_self_pd (p : Fin sys.rs.n) : right p ≠ p := by
  intro h
  have hval := congrArg Fin.val h
  simp only [right_val] at hval
  have hp := p.isLt
  have hn := sys.rs.n_ge_4
  by_cases h1 : p.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt h1] at hval; omega
  · rw [show p.val + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega

/-! ### Neighbor preservation at firing steps -/

/-- **Left-neighbor preservation**: if binary processor p fires at step k,
    then the value at left(p) in the NEXT config equals the value at
    left(p) in the CURRENT config (since only p changes, and left(p) ≠ p). -/
theorem left_val_preserved_at_firing (gc : GoodCycle sys)
    (k : Fin gc.configs.length) (p : Fin sys.rs.n)
    (hmov : gc.moverAt k = p) :
    (gc.configs.get (nextIndex gc.configs k)) (left p) =
      (gc.configs.get k) (left p) := by
  have hne : left p ≠ gc.moverAt k := by
    rw [hmov]; exact left_ne_self_pd p
  exact gc.state_eq_of_ne_moverAt k (left p) hne

/-- **Right-neighbor preservation**: similarly for right(p). -/
theorem right_val_preserved_at_firing (gc : GoodCycle sys)
    (k : Fin gc.configs.length) (p : Fin sys.rs.n)
    (hmov : gc.moverAt k = p) :
    (gc.configs.get (nextIndex gc.configs k)) (right p) =
      (gc.configs.get k) (right p) := by
  have hne : right p ≠ gc.moverAt k := by
    rw [hmov]; exact right_ne_self_pd p
  exact gc.state_eq_of_ne_moverAt k (right p) hne

/-- **Complete local context preservation**: at a step where p fires,
    every position j with j ≠ p retains its value. -/
theorem full_context_at_firing (gc : GoodCycle sys)
    (k : Fin gc.configs.length) (p j : Fin sys.rs.n)
    (hmov : gc.moverAt k = p) (hj : j ≠ p) :
    (gc.configs.get (nextIndex gc.configs k)) j =
      (gc.configs.get k) j :=
  gc.state_eq_of_ne_moverAt k j (by rw [hmov]; exact hj)

/-! ### Parallel orbit: the shadow-config engine -/

/-- Helper: if gc.moverAt k = p and q = left p, then gc.moverAt k ≠ left (left p)
    requires the ring argument that left p ≠ left (left p), which we get from
    the fact that left is injective (right ∘ left = id). -/
private theorem ne_of_ne_right_left (p q : Fin sys.rs.n) (_h : p ≠ q) :
    left p ≠ q → p ≠ right q := by
  intro hlp hrq
  exact hlp (by rw [hrq]; simp [left_right_eq_self])

private theorem ne_of_ne_left_right (p q : Fin sys.rs.n) (_h : p ≠ q) :
    right p ≠ q → p ≠ left q := by
  intro hrp hlq
  exact hrp (by rw [hlq]; simp [right_left_eq_self])

/-- **Product decomposition for parallel orbits.**

    Given a good cycle and a config c that agrees with gc.configs[k] at
    all positions except possibly position q (where q is far from the
    mover), moving c by the same mover as the good cycle produces a
    config that agrees with gc.configs[k+1] at all non-q positions.

    This is the engine behind the shadow-config construction in
    `CaseObstructions.lean`: we can flip q to any value and track the
    parallel orbit. -/
theorem parallel_move_preserves_agreement (gc : GoodCycle sys)
    (k : Fin gc.configs.length) (c : Config sys.rs)
    (q : Fin sys.rs.n)
    (hq_ne_mover : gc.moverAt k ≠ q)
    (hq_ne_left : gc.moverAt k ≠ left q)
    (hq_ne_right : gc.moverAt k ≠ right q)
    (hagree : ∀ j, j ≠ q → c j = (gc.configs.get k) j) :
    ∀ j, j ≠ q →
      (move sys c (gc.moverAt k)) j =
        (gc.configs.get (nextIndex gc.configs k)) j := by
  intro j hj
  rw [gc.step_eq_move k]
  -- c and gc.configs.get k agree at left(moverAt k), moverAt k, right(moverAt k)
  -- since none of these equal q
  have hL : c (left (gc.moverAt k)) = (gc.configs.get k) (left (gc.moverAt k)) := by
    apply hagree
    intro heq
    -- left(moverAt k) = q implies moverAt k = right q (since right ∘ left = id)
    have : gc.moverAt k = right q := by
      calc gc.moverAt k = right (left (gc.moverAt k)) := by simp [right_left_eq_self]
        _ = right q := by rw [heq]
    exact hq_ne_right this
  have hS : c (gc.moverAt k) = (gc.configs.get k) (gc.moverAt k) := by
    apply hagree
    intro heq; exact hq_ne_mover heq
  have hR : c (right (gc.moverAt k)) = (gc.configs.get k) (right (gc.moverAt k)) := by
    apply hagree
    intro heq
    -- right(moverAt k) = q implies moverAt k = left q (since left ∘ right = id)
    have : gc.moverAt k = left q := by
      calc gc.moverAt k = left (right (gc.moverAt k)) := by simp [left_right_eq_self]
        _ = left q := by rw [heq]
    exact hq_ne_left this
  by_cases hjm : j = gc.moverAt k
  · -- At mover: local context agrees, so transition produces same value
    subst hjm
    exact move_same_at_mover_of_local_agree c (gc.configs.get k) (gc.moverAt k) hL hS hR
  · -- At non-mover: move doesn't change j's value
    simp [move, hjm, hagree j hj]

/-- **Parallel orbit preserves privileged status.**

    If c agrees with gc.configs[k] at all positions except q, and the
    mover at step k is far from q, then the mover is privileged at c. -/
theorem parallel_orbit_privileged (gc : GoodCycle sys)
    (k : Fin gc.configs.length) (c : Config sys.rs)
    (q : Fin sys.rs.n)
    (hq_ne_mover : gc.moverAt k ≠ q)
    (hq_ne_left : gc.moverAt k ≠ left q)
    (hq_ne_right : gc.moverAt k ≠ right q)
    (hagree : ∀ j, j ≠ q → c j = (gc.configs.get k) j) :
    privileged sys c (gc.moverAt k) := by
  apply privileged_of_local_eq (gc.configs.get k) c (gc.moverAt k)
  · exact (hagree (left (gc.moverAt k)) (by
      intro heq
      have : gc.moverAt k = right q := by
        calc gc.moverAt k = right (left (gc.moverAt k)) := by simp [right_left_eq_self]
          _ = right q := by rw [heq]
      exact hq_ne_right this)).symm
  · exact (hagree (gc.moverAt k) (by
      intro heq; exact hq_ne_mover heq)).symm
  · exact (hagree (right (gc.moverAt k)) (by
      intro heq
      have : gc.moverAt k = left q := by
        calc gc.moverAt k = left (right (gc.moverAt k)) := by simp [left_right_eq_self]
          _ = left q := by rw [heq]
      exact hq_ne_left this)).symm
  · exact gc.moverAt_privileged k

/-! ### Decomposition into independent arcs -/

/-- An arc on the ring: positions from `start` going clockwise for `len` steps.
    (Empty arc if len = 0.) -/
def arcMem (n : Nat) (start : Fin n) (len : Nat) (j : Fin n) : Prop :=
  ∃ d : Nat, d < len ∧ j.val = (start.val + d) % n

/-- **Independent arc evolution**: if the mover is outside the arc,
    then move preserves agreement on the arc.

    Since j's value doesn't change when j ≠ mover, and mover ∉ arc,
    every arc position retains its pre-move value. -/
theorem move_preserves_arc_values (c₁ c₂ : Config sys.rs)
    (mover : Fin sys.rs.n) (start : Fin sys.rs.n) (len : Nat)
    (hagree : AgreeOn c₁ c₂ (arcMem sys.rs.n start len))
    (hmover_outside : ¬arcMem sys.rs.n start len mover) :
    AgreeOn (move sys c₁ mover) (move sys c₂ mover) (arcMem sys.rs.n start len) := by
  intro j hj
  have hjm : j ≠ mover := fun h => hmover_outside (h ▸ hj)
  simp [move, hjm, hagree j hj]

/-! ### Phase-shift value preservation -/

/-- **Phase-shift entry conflict**: if processor q does not fire during
    steps a..b-1 (where a, b < configs.length), then q's config value
    is the same at steps a and b. -/
theorem val_preserved_between_firings (gc : GoodCycle sys)
    (q : Fin sys.rs.n)
    {a b : Nat} (ha : a < gc.configs.length) (hb : b < gc.configs.length)
    (hab : a ≤ b)
    (hno : ∀ (k : Nat) (hk : k < gc.configs.length), a ≤ k → k < b → gc.moverAt ⟨k, hk⟩ ≠ q) :
    (gc.configs.get ⟨b, hb⟩) q = (gc.configs.get ⟨a, ha⟩) q :=
  gc_config_const_if_no_fire gc q hab hb ha hno

end LeanMn
