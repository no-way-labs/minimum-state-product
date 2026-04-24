/-
  BinaryParity.lean — State preservation utilities for the lower bound proof

  Two lemmas:
  1. `state_eq_of_noFire_between`: if processor p does not fire in [t₀, t₁),
     its state is preserved.
  2. `binary_state_eq_of_even_fireCount`: if a binary processor fires an even
     number of times in [t₀, t₁), its state is preserved.
-/
import LeanMn.LowerBound.EntryConflict.ContextBridge

namespace LeanMn

variable {sys : System}

/-! ### Lemma 1: State preservation when a processor does not fire -/

/-- If processor `p` does not fire at any step in `[t₀, t₁)`, then its
    configuration value is preserved: `configAt t₀ p = configAt t₁ p`.

    This is a direct re-export of `configVal_eq_of_noFire_between` with
    a more discoverable name. -/
theorem state_eq_of_noFire_between
    (gc : GoodCycle sys) (p : Fin sys.rs.n) (t₀ t₁ : Nat)
    (hle : t₀ ≤ t₁) (ht₁ : t₁ < gc.configs.length)
    (hno : ∀ k : Fin gc.configs.length,
      t₀ ≤ k.val → k.val < t₁ → gc.moverAt k ≠ p) :
    (gc.configs.get ⟨t₀, lt_of_le_of_lt hle ht₁⟩) p =
      (gc.configs.get ⟨t₁, ht₁⟩) p :=
  configVal_eq_of_noFire_between gc p t₀ t₁ hle ht₁ hno

/-! ### Interval fire count -/

/-- Number of times processor `p` fires in `[a, b)`. -/
noncomputable def GoodCycle.intervalFireCount (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (a b : Nat) : Nat :=
  gc.prefixFireCount p b - gc.prefixFireCount p a

private theorem prefixFireCount_mono (gc : GoodCycle sys)
    (p : Fin sys.rs.n) {a b : Nat} (hab : a ≤ b) :
    gc.prefixFireCount p a ≤ gc.prefixFireCount p b := by
  unfold GoodCycle.prefixFireCount
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hab)

private theorem intervalFireCount_eq_sub (gc : GoodCycle sys)
    (p : Fin sys.rs.n) {a b : Nat} (_hab : a ≤ b) :
    gc.intervalFireCount p a b = gc.prefixFireCount p b - gc.prefixFireCount p a := by
  rfl

private theorem prefixFireCount_split (gc : GoodCycle sys)
    (p : Fin sys.rs.n) {a b : Nat} (hab : a ≤ b) :
    gc.prefixFireCount p b = gc.prefixFireCount p a + gc.intervalFireCount p a b := by
  rw [intervalFireCount_eq_sub gc p hab]
  have := prefixFireCount_mono gc p hab
  omega

/-! ### Lemma 2: Binary state preservation under even fire count -/

/-- If a binary processor `p` (modulus 2) fires an even number of times
    in `[t₀, t₁)`, then its configuration value is preserved:
    `configAt t₀ p = configAt t₁ p`.

    Proof: by the binary parity theorem, the state after `m` steps is
    `(initial + prefixFireCount m) % 2`. Two times give the same state
    iff their prefix fire counts have the same parity, which holds
    exactly when the interval fire count is even. -/
theorem binary_state_eq_of_even_fireCount
    (gc : GoodCycle sys) (p : Fin sys.rs.n) (hbin : sys.rs.m p = 2)
    (t₀ t₁ : Nat) (hle : t₀ ≤ t₁) (ht₁ : t₁ ≤ gc.configs.length)
    (heven : Even (gc.intervalFireCount p t₀ t₁)) :
    gc.stateAfter p t₀ = gc.stateAfter p t₁ := by
  rw [gc.binary_stateAfter_eq_iff_prefixFireCount_modEq p hbin
    (le_trans hle ht₁) ht₁]
  -- Need: prefixFireCount p t₀ % 2 = prefixFireCount p t₁ % 2
  -- From heven: intervalFireCount p t₀ t₁ is even
  -- intervalFireCount = prefixFireCount t₁ - prefixFireCount t₀
  have hmono := prefixFireCount_mono gc p hle
  have hsplit := prefixFireCount_split gc p hle
  obtain ⟨k, hk⟩ := heven
  rw [intervalFireCount_eq_sub gc p hle] at hk
  omega

/-- Variant of `binary_state_eq_of_even_fireCount` stated in terms of
    `configs.get` rather than `stateAfter`, for steps strictly inside the
    cycle. -/
theorem binary_config_eq_of_even_intervalFireCount
    (gc : GoodCycle sys) (p : Fin sys.rs.n) (hbin : sys.rs.m p = 2)
    (t₀ t₁ : Nat) (hle : t₀ ≤ t₁) (ht₁ : t₁ < gc.configs.length)
    (heven : Even (gc.intervalFireCount p t₀ t₁)) :
    (gc.configs.get ⟨t₀, lt_of_le_of_lt hle ht₁⟩) p =
      (gc.configs.get ⟨t₁, ht₁⟩) p := by
  have h₀ := gc.stateAfter_of_lt p (lt_of_le_of_lt hle ht₁)
  have h₁ := gc.stateAfter_of_lt p ht₁
  have heq := binary_state_eq_of_even_fireCount gc p hbin t₀ t₁ hle
    (Nat.le_of_lt ht₁) heven
  rw [h₀, h₁] at heq
  exact Fin.val_injective (congrArg Fin.val heq)

end LeanMn
