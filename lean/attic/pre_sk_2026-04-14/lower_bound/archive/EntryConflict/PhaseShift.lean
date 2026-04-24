/-
  PhaseShift.lean — Binary fireCount ≥ 4 propagation + gc.distinct contradiction

  Main results:
  1. `propagate_all_fire`: if no consecutive pair of p-fires is followed by a non-p
     step, then ALL steps fire at p.
  2. `all_fire_False`: if all steps fire at binary p (with L ≥ 4), then
     configs at steps 1 and 3 coincide, contradicting gc.distinct.
-/
import LeanMn.LowerBound.EntryConflict.NestedFirings

namespace LeanMn

variable {sys : System}

/-! ### All processors fire at p → False via gc.distinct -/

/-- If binary p fires at EVERY step, configs at step 1 and step 3 are identical,
    contradicting gc.distinct. Requires L ≥ 4. -/
theorem all_fire_False
    (gc : GoodCycle sys) (p : Fin sys.rs.n) (hbin : isBinary sys.rs p)
    (hL4 : gc.configs.length ≥ 4)
    (hall : ∀ k : Fin gc.configs.length, gc.moverAt k = p) :
    False := by
  have h1 : (1 : Nat) < gc.configs.length := by omega
  have h3 : (3 : Nat) < gc.configs.length := by omega
  -- All non-p processors have constant value (only p fires)
  have hconst : ∀ (j : Fin sys.rs.n) (_ : j ≠ p) (k : Fin gc.configs.length),
      (gc.configs.get k) j = (gc.configs.get ⟨0, gc.configs_length_pos⟩) j := by
    intro j hj ⟨m, hm⟩
    induction m with
    | zero => rfl
    | succ m ih =>
      have hm' : m < gc.configs.length := by omega
      by_cases hlt : m + 1 < gc.configs.length
      · have hnext : (⟨m + 1, hlt⟩ : Fin gc.configs.length) =
            nextIndex gc.configs ⟨m, hm'⟩ :=
          Fin.ext (Nat.mod_eq_of_lt hlt).symm
        rw [show (⟨m + 1, hm⟩ : Fin gc.configs.length) = ⟨m + 1, hlt⟩ from Fin.ext rfl,
            hnext, gc.state_eq_of_ne_moverAt ⟨m, hm'⟩ j (by rw [hall]; exact hj)]
        exact ih hm'
      · omega
  -- prefixFireCount at step k = k (fires at every step)
  have hpfc : ∀ k : Nat, k ≤ gc.configs.length → gc.prefixFireCount p k = k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [gc.prefixFireCount_succ, ih (by omega),
          gc.fireIndicator_of_lt p (by omega : k < gc.configs.length)]
      simp [hall ⟨k, by omega⟩]
  -- stateAfter 1 = stateAfter 3 (both odd: (v+1)%2 = (v+3)%2)
  have h13 : gc.stateAfter p 1 = gc.stateAfter p 3 := by
    have hpval := gc.binary_stateAfter_val_eq_initial_add_prefix p hbin
    apply Fin.ext
    rw [hpval 1 (by omega), hpval 3 (by omega), hpfc 1 (by omega), hpfc 3 (by omega)]
    omega
  -- configs.get 1 = configs.get 3
  have hcfg : gc.configs.get ⟨1, h1⟩ = gc.configs.get ⟨3, h3⟩ := by
    funext j
    by_cases hjp : j = p
    · rw [hjp, ← gc.stateAfter_of_lt p h1, ← gc.stateAfter_of_lt p h3]; exact h13
    · rw [hconst j hjp ⟨1, h1⟩, hconst j hjp ⟨3, h3⟩]
  -- gc.distinct: index 1 = index 3 → 1 = 3 → contradiction
  have h13idx := gc.distinct ⟨1, h1⟩ ⟨3, h3⟩ hcfg
  exact absurd h13idx (by intro h; have := congrArg Fin.val h; simp at this)

/-! ### Propagation: no boundary → all fire -/

/-- If every consecutive pair of p-fires has a p-fire right after it,
    then starting from a known pair, ALL steps fire at p.

    This is the key propagation lemma: by contradiction, if no
    consecutive pair is followed by a non-p step, then all steps
    fire at p (from the initial pair, propagate forward around the ring). -/
theorem propagate_all_fire
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (a : Fin gc.configs.length)
    (ha : gc.moverAt a = p)
    (ha1 : gc.moverAt (nextIndex gc.configs a) = p)
    (hno : ∀ x : Fin gc.configs.length,
      gc.moverAt x = p → gc.moverAt (nextIndex gc.configs x) = p →
      gc.moverAt (nextIndex gc.configs (nextIndex gc.configs x)) = p) :
    ∀ k : Fin gc.configs.length, gc.moverAt k = p := by
  have hLpos := gc.configs_length_pos
  -- Key modular arithmetic: (x % L + 1) % L = (x + 1) % L
  have mod_succ : ∀ x : Nat, (x % gc.configs.length + 1) % gc.configs.length =
      (x + 1) % gc.configs.length := by
    intro x
    set n := gc.configs.length
    have hdm := Nat.div_add_mod x n
    conv_rhs => rw [show x + 1 = x % n + n * (x / n) + 1 from by omega]
    rw [show x % n + n * (x / n) + 1 = x % n + 1 + n * (x / n) from by omega]
    rw [Nat.add_mul_mod_self_left]
  -- Prove pair invariant by induction
  suffices hpair : ∀ d : Nat,
      gc.moverAt ⟨(a.val + d) % gc.configs.length, Nat.mod_lt _ hLpos⟩ = p ∧
      gc.moverAt ⟨(a.val + d + 1) % gc.configs.length, Nat.mod_lt _ hLpos⟩ = p by
    intro k
    have hd_eq : (a.val + (k.val + gc.configs.length - a.val) % gc.configs.length) % gc.configs.length = k.val := by
      have := k.isLt; have := a.isLt
      by_cases hka : a.val ≤ k.val
      · rw [show k.val + gc.configs.length - a.val = (k.val - a.val) + gc.configs.length from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : k.val - a.val < gc.configs.length),
            show a.val + (k.val - a.val) = k.val from by omega,
            Nat.mod_eq_of_lt (by omega)]
      · rw [Nat.mod_eq_of_lt (by omega : k.val + gc.configs.length - a.val < gc.configs.length),
            show a.val + (k.val + gc.configs.length - a.val) = k.val + gc.configs.length from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have := (hpair ((k.val + gc.configs.length - a.val) % gc.configs.length)).1
    convert this using 2; exact Fin.ext hd_eq.symm
  intro d
  induction d with
  | zero =>
    refine ⟨?_, ?_⟩
    · -- (a.val + 0) % L = a.val
      have : (a.val + 0) % gc.configs.length = a.val := by
        rw [Nat.add_zero]; exact Nat.mod_eq_of_lt a.isLt
      simp only [this]; exact ha
    · exact ha1
  | succ d ih =>
    obtain ⟨ihd, ihd1⟩ := ih
    refine ⟨ihd1, ?_⟩
    have hnext_eq : nextIndex gc.configs ⟨(a.val + d) % gc.configs.length, Nat.mod_lt _ hLpos⟩ =
        ⟨(a.val + d + 1) % gc.configs.length, Nat.mod_lt _ hLpos⟩ := by
      ext; show ((a.val + d) % gc.configs.length + 1) % gc.configs.length = (a.val + d + 1) % gc.configs.length
      exact mod_succ (a.val + d)
    have h2 := hno ⟨(a.val + d) % gc.configs.length, _⟩ ihd (by rw [hnext_eq]; exact ihd1)
    rw [hnext_eq] at h2
    -- Goal: moverAt ⟨(a + (d+1) + 1) % L, _⟩ = p
    -- h2: moverAt (nextIndex ⟨(a+d+1)%L, _⟩) = p
    -- nextIndex ⟨(a+d+1)%L, _⟩ = ⟨((a+d+1)%L+1)%L, _⟩ = ⟨(a+d+2)%L, _⟩
    -- (a+(d+1)+1) = (a+d+2)
    -- So the Fin values are equal: (a+(d+1)+1)%L = (a+d+2)%L (by ring_nf).
    -- And (a+d+2)%L = ((a+d+1)%L+1)%L (by mod_succ).
    -- h2 has type: moverAt ⟨((a+d+1)%L+1)%L, _⟩ = p
    -- We need: moverAt ⟨(a+(d+1)+1)%L, _⟩ = p
    -- These Fins have the same .val by the above.
    convert h2 using 2
    ext
    show (a.val + (d + 1) + 1) % gc.configs.length = ((a.val + d + 1) % gc.configs.length + 1) % gc.configs.length
    rw [show a.val + (d + 1) + 1 = a.val + d + 1 + 1 from by ring]
    exact (mod_succ (a.val + d + 1)).symm

end LeanMn
