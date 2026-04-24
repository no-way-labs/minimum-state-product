/-
  LowerBound/SK/SinkKernel.lean — Sink-kernel definition + T1 soundness
-/
import LeanMn.LowerBound.SK.Forcing

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LeanMn.SK

variable {sys : System}

noncomputable def removeOnce (D : DetDict sys) (S : Finset (Config sys.rs)) :
    Finset (Config sys.rs) :=
  S.filter fun c => hasForcedNeighborIn D c S

theorem removeOnce_subset (D : DetDict sys) (S : Finset (Config sys.rs)) :
    removeOnce D S ⊆ S :=
  Finset.filter_subset _ _

noncomputable def iterateRemove (D : DetDict sys)
    (S : Finset (Config sys.rs)) : ℕ → Finset (Config sys.rs)
  | 0 => S
  | n + 1 => removeOnce D (iterateRemove D S n)

theorem iterateRemove_subset (D : DetDict sys) (S : Finset (Config sys.rs))
    (n : ℕ) : iterateRemove D S n ⊆ S := by
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ k ih => exact Finset.Subset.trans (removeOnce_subset _ _) ih

theorem iterateRemove_card_antitone (D : DetDict sys) (S : Finset (Config sys.rs))
    (n : ℕ) : (iterateRemove D S (n + 1)).card ≤ (iterateRemove D S n).card :=
  Finset.card_le_card (removeOnce_subset _ _)

theorem removeOnce_eq_of_card_eq (D : DetDict sys) (S : Finset (Config sys.rs))
    (h : (removeOnce D S).card = S.card) :
    removeOnce D S = S :=
  Finset.eq_of_subset_of_card_le (removeOnce_subset D S) (le_of_eq h.symm)

/-- Shift: iterateRemove D S (m+1) = iterateRemove D (removeOnce D S) m. -/
theorem iterateRemove_shift (D : DetDict sys) (S : Finset (Config sys.rs))
    (m : ℕ) : iterateRemove D S (m + 1) = iterateRemove D (removeOnce D S) m := by
  induction m with
  | zero => rfl
  | succ k ih => show removeOnce D _ = removeOnce D _; congr 1

/-- A non-increasing ℕ sequence stabilizes after at most f(0) steps. -/
theorem iterateRemove_stabilize (D : DetDict sys) (S : Finset (Config sys.rs))
    (n : ℕ) (hn : S.card ≤ n) :
    iterateRemove D S (n + 1) = iterateRemove D S n := by
  induction n generalizing S with
  | zero =>
    have : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hn)
    simp [iterateRemove, removeOnce, this]
  | succ k ih =>
    by_cases heq : removeOnce D S = S
    · -- S is already a fixed point
      suffices h : ∀ m, iterateRemove D S m = S from by simp [h]
      intro m; induction m with
      | zero => rfl
      | succ j ihj => simp [iterateRemove, ihj, heq]
    · -- Strict decrease in cardinality
      have hcard_lt : (removeOnce D S).card < S.card := by
        have hle := Finset.card_le_card (removeOnce_subset D S)
        have hne : (removeOnce D S).card ≠ S.card :=
          fun h => heq (removeOnce_eq_of_card_eq D S h)
        omega
      have hle : (removeOnce D S).card ≤ k := by omega
      rw [iterateRemove_shift D S (k + 1), iterateRemove_shift D S k]
      exact ih (removeOnce D S) hle

/-! ## SK definition and properties -/

noncomputable def SK (gc : GoodCycle sys) : Finset (Config sys.rs) :=
  let D := detOf gc
  let ng := (Finset.univ : Finset (Config sys.rs)).filter (NonGood gc)
  iterateRemove D ng (Fintype.card (Config sys.rs))

theorem SK_subset_nonGood (gc : GoodCycle sys) :
    ∀ c ∈ SK gc, NonGood gc c := by
  intro c hc
  have := iterateRemove_subset _ _ _ hc
  exact (Finset.mem_filter.mp this).2

theorem SK_eq_removeOnce (gc : GoodCycle sys) :
    removeOnce (detOf gc) (SK gc) = SK gc := by
  simp only [SK]
  exact iterateRemove_stabilize _ _ _
    (le_trans (Finset.card_filter_le _ _) (by simp))

theorem SK_closed (gc : GoodCycle sys) :
    ∀ c ∈ SK gc, ∃ c' ∈ (SK gc), c' ∈ forcedNeighbors (detOf gc) c := by
  intro c hc
  rw [← SK_eq_removeOnce gc] at hc
  simp only [removeOnce, Finset.mem_filter] at hc
  simp only [hasForcedNeighborIn, List.any_eq_true, decide_eq_true_eq] at hc
  obtain ⟨_, c', hc'_nbrs, hc'_SK⟩ := hc
  exact ⟨c', hc'_SK, hc'_nbrs⟩

/-! ## Monotonicity and closed-subset bridge

`iterateRemove` is monotone in its starting set: adding elements can
only add survivors. A forced-closed subset — every element has a
forced successor staying inside — is a fixed point of `iterateRemove`.
Combined, any nonempty forced-closed subset of the NonGood set sits
inside `SK`, proving `SK.Nonempty`. -/

theorem removeOnce_mono (D : DetDict sys) {S T : Finset (Config sys.rs)}
    (hST : S ⊆ T) : removeOnce D S ⊆ removeOnce D T := by
  intro c hc
  have hcS : c ∈ S := (Finset.mem_filter.mp hc).1
  have hcT : c ∈ T := hST hcS
  have hforced : hasForcedNeighborIn D c S = true :=
    (Finset.mem_filter.mp hc).2
  have hforcedT : hasForcedNeighborIn D c T = true := by
    simp only [hasForcedNeighborIn, List.any_eq_true, decide_eq_true_eq] at hforced ⊢
    obtain ⟨c', hc'nbr, hc'S⟩ := hforced
    exact ⟨c', hc'nbr, hST hc'S⟩
  exact Finset.mem_filter.mpr ⟨hcT, hforcedT⟩

theorem iterateRemove_mono (D : DetDict sys)
    {S T : Finset (Config sys.rs)} (hST : S ⊆ T) (n : ℕ) :
    iterateRemove D S n ⊆ iterateRemove D T n := by
  induction n with
  | zero => exact hST
  | succ k ih => exact removeOnce_mono D ih

/-- A forced-closed subset is a fixed point of `removeOnce`. -/
theorem removeOnce_eq_of_forced_closed (D : DetDict sys)
    (S : Finset (Config sys.rs))
    (hclosed : ∀ c ∈ S, ∃ c' ∈ S, c' ∈ forcedNeighbors D c) :
    removeOnce D S = S := by
  apply Finset.Subset.antisymm (removeOnce_subset D S)
  intro c hc
  refine Finset.mem_filter.mpr ⟨hc, ?_⟩
  simp only [hasForcedNeighborIn, List.any_eq_true, decide_eq_true_eq]
  obtain ⟨c', hc'S, hc'nbr⟩ := hclosed c hc
  exact ⟨c', hc'nbr, hc'S⟩

theorem iterateRemove_eq_of_forced_closed (D : DetDict sys)
    (S : Finset (Config sys.rs))
    (hclosed : ∀ c ∈ S, ∃ c' ∈ S, c' ∈ forcedNeighbors D c)
    (n : ℕ) : iterateRemove D S n = S := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show removeOnce D (iterateRemove D S k) = S
    rw [ih]; exact removeOnce_eq_of_forced_closed D S hclosed

/-- **SK bridge lemma.** Any nonempty subset of NG that is closed under
    forced successors lies inside `SK gc`. Consequently `SK gc` is
    nonempty. This is the Outcome-A reduction: the main-theorem hook
    only needs `.Nonempty`, and this lemma produces that from any
    structural witness of a closed forced chain. -/
theorem sk_nonempty_of_closed_forced_subset
    (gc : GoodCycle sys) (S : Finset (Config sys.rs))
    (hSne : S.Nonempty)
    (hSng : ∀ c ∈ S, NonGood gc c)
    (hSclosed : ∀ c ∈ S,
      ∃ c' ∈ S, c' ∈ forcedNeighbors (detOf gc) c) :
    (SK gc).Nonempty := by
  let ng := (Finset.univ : Finset (Config sys.rs)).filter (NonGood gc)
  have hSsubNG : S ⊆ ng := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSng c hc⟩
  obtain ⟨c₀, hc₀⟩ := hSne
  refine ⟨c₀, ?_⟩
  have hfix :
      iterateRemove (detOf gc) S (Fintype.card (Config sys.rs)) = S :=
    iterateRemove_eq_of_forced_closed (detOf gc) S hSclosed _
  have hmono :
      iterateRemove (detOf gc) S (Fintype.card (Config sys.rs)) ⊆
        iterateRemove (detOf gc) ng (Fintype.card (Config sys.rs)) :=
    iterateRemove_mono (detOf gc) hSsubNG _
  have hc₀_S : c₀ ∈ iterateRemove (detOf gc) S (Fintype.card (Config sys.rs)) := by
    rw [hfix]; exact hc₀
  exact hmono hc₀_S

/-! ## T1: SK nonempty → ¬converges -/

/-- The det records sys.f at any context that produces a forced edge.
    If detOf returns some v with v ≠ s (a move, not a stay), then
    v = sys.f i l s r.

    Proof: the only det entries with output ≠ input come from mover
    steps in the cycle. At mover step k with mover p, the value
    inserted is c_{k+1}[p] = (move sys c_k p)[p] = sys.f p l s r.
    Non-mover entries have output = input (stay), so v ≠ s excludes them. -/
theorem detOf_move_eq_sysf (gc : GoodCycle sys)
    (i : Fin sys.rs.n) (l : Fin (sys.rs.m (left i)))
    (s : Fin (sys.rs.m i)) (r : Fin (sys.rs.m (right i)))
    (v : Fin (sys.rs.m i))
    (hdet : detOf gc i l s r = some v) (hne : v ≠ s) :
    v = sys.f i l s r := by
  -- Unfold detOf: it found a step k matching context (l, s, r) at position i,
  -- and returned c_{k+1}[i].
  simp only [detOf] at hdet
  -- Extract the matching step k
  generalize hfind : (List.finRange gc.configs.length).find?
    (fun k => (gc.configs.get k (left i) == l) &&
              (gc.configs.get k i == s) &&
              (gc.configs.get k (right i) == r)) = found at hdet
  cases found with
  | none => simp at hdet
  | some k =>
    -- hdet : some v = some (gc.configs.get (nextIndex gc.configs k) i)
    -- So v = that value
    have hv : v = gc.configs.get (nextIndex gc.configs k) i := by
      simpa using hdet.symm
    -- The find? guarantees the context matches at step k
    have hmatch := List.find?_some hfind
    simp [Bool.and_eq_true, beq_iff_eq] at hmatch
    obtain ⟨⟨hl, hs⟩, hr⟩ := hmatch
    -- Case split: is i the mover at step k?
    by_cases hmov : i = gc.moverAt k
    · -- i IS the mover: c_{k+1}[i] = sys.f i l s r
      -- c_{k+1} = move sys c_k p (by step_eq_move)
      -- (move sys c_k p) i with i = p gives sys.f i l s r
      have hstep := gc.step_eq_move k
      -- Substitute i = moverAt k everywhere
      subst hmov
      conv at hv => rhs; rw [hstep]
      simp only [move, dite_true] at hv
      -- hv : v = Fin.cast ... (sys.f (moverAt k) ...)
      -- Goal: v = sys.f (moverAt k) l s r
      -- The Fin.cast is an identity cast, and l/s/r match
      -- hv now has the form: v = Fin.cast _ (sys.f (moverAt k) (c_k ...) (c_k ...) (c_k ...))
      -- and hl/hs/hr say c_k's values at the neighbors match l/s/r
      -- Goal: v = sys.f (moverAt k) l s r
      -- hv : v = Fin.cast _ (sys.f (moverAt k) (c.get k (left _)) (c.get k _) (c.get k (right _)))
      -- hl : c.get k (left _) = l,  hs : c.get k _ = s,  hr : c.get k (right _) = r
      subst hl; subst hs; subst hr
      rw [hv]; simp [Fin.cast_eq_self]
    · -- i is NOT the mover: c_{k+1}[i] = c_k[i] = s
      -- But then v = s, contradicting hne
      have hstay := gc.state_eq_of_ne_moverAt k i hmov
      -- hstay : c_{k+1}[i] = c_k[i]
      rw [hv, hstay] at hne
      exact absurd hs hne

/-- A forced neighbor under detOf is a valid step of the system. -/
theorem forcedNeighbor_is_step (gc : GoodCycle sys)
    (c c' : Config sys.rs) (h : c' ∈ forcedNeighbors (detOf gc) c) :
    step sys c c' := by
  simp only [forcedNeighbors, List.mem_filterMap] at h
  obtain ⟨p, _, hp⟩ := h
  -- hp : (match forcedOutput ... with | some v => some (applyMove c p v) | none => none) = some c'
  simp only [forcedOutput] at hp
  -- Split on whether detOf returns some or none
  generalize hdet : detOf gc p (c (left p)) (c p) (c (right p)) = dval at hp
  cases dval with
  | none => simp at hp
  | some v =>
    -- Split on whether v = c p
    by_cases hne : v = c p
    · simp [hne] at hp
    · simp [hne] at hp
      -- hp : c' = applyMove c p v
      have hv := detOf_move_eq_sysf gc p (c (left p)) (c p) (c (right p)) v hdet hne
      refine ⟨p, ?_, ?_⟩
      · -- privileged: sys.f ≠ c p
        simp only [privileged]; rw [← hv]; exact hne
      · -- c' = move sys c p
        subst hp; funext j; simp only [applyMove, move]
        by_cases hj : j = p
        · subst hj; simp [hv]
        · simp [hj]

/-- Standard: if every element in S has a predecessor in S under R,
    no element of S is R-accessible. -/
private theorem not_acc_of_infinite_descent {α : Type*} {R : α → α → Prop}
    (S : Finset α) (hdesc : ∀ a ∈ S, ∃ b ∈ S, R b a) :
    ∀ a, a ∈ S → ¬Acc R a := by
  intro a ha hacc
  induction hacc with
  | intro x _ ih =>
    obtain ⟨y, hy_mem, hy_rel⟩ := hdesc x ha
    exact ih y hy_rel hy_mem

theorem not_converges_of_SK_nonempty
    (gc : GoodCycle sys) (hSK : (SK gc).Nonempty) :
    ¬ converges sys gc := by
  intro hconv
  obtain ⟨c₀, hc₀⟩ := hSK
  have hbad : ∀ c ∈ SK gc, ∃ c' ∈ SK gc, badStep sys gc c' c := by
    intro c hc
    obtain ⟨c', hc'sk, hc'forced⟩ := SK_closed gc c hc
    exact ⟨c', hc'sk,
           SK_subset_nonGood gc c hc,
           SK_subset_nonGood gc c' hc'sk,
           forcedNeighbor_is_step gc c c' hc'forced⟩
  exact absurd (hconv.apply c₀) (not_acc_of_infinite_descent (SK gc) hbad c₀ hc₀)

/-- More general T1 soundness: any nonempty finite set of non-good
    configurations that is closed under forced successors witnesses
    non-convergence. -/
theorem not_converges_of_closed_forced_set
    (gc : GoodCycle sys) (S : Finset (Config sys.rs))
    (hS : S.Nonempty)
    (hbad : ∀ c ∈ S, NonGood gc c)
    (hclosed : ∀ c ∈ S, ∃ c' ∈ S, c' ∈ forcedNeighbors (detOf gc) c) :
    ¬ converges sys gc := by
  intro hconv
  obtain ⟨c₀, hc₀⟩ := hS
  have hdesc : ∀ c ∈ S, ∃ c' ∈ S, badStep sys gc c' c := by
    intro c hc
    obtain ⟨c', hc'S, hc'forced⟩ := hclosed c hc
    exact ⟨c', hc'S, hbad c hc, hbad c' hc'S,
      forcedNeighbor_is_step gc c c' hc'forced⟩
  exact absurd (hconv.apply c₀) (not_acc_of_infinite_descent S hdesc c₀ hc₀)

end LeanMn.SK
