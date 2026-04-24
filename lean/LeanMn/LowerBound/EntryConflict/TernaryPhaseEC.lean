/-
  TernaryPhaseEC.lean — Three entry conflict mechanisms for ternary phases

  Setup: ternary processor t sandwiched between binary bL = left(t)
  and bR = right(t). In a phase where c[t] is constant:

  **Mechanism 1 (Both-Even Return):**  M=1, J even, K even.
  Both binary neighbors return to their original values → mover context
  matches an earlier nonmover context.

  **Mechanism 2 (Toggle-FR):**  any M ≥ 1, J ≥ 2, K = 0 (or symmetric).
  bR doesn't fire (constant), bL fires ≥2 times. Since bL is binary,
  among its firings t sees nonmover contexts with both bL values (0 and 1).
  t's mover context must match one of them (binary has only 2 values).

  **Mechanism 3 (Zero-Side EC):**  M = 1, J ≥ 2, K = 0 (or symmetric).
  Same argument as Toggle-FR. Stated separately because the hypotheses
  (M=1) allow a cleaner interface: only one mover step exists, and
  bR's constancy follows from it not firing in the entire phase.
-/
import LeanMn.LowerBound.EntryConflict.BinaryParity

namespace LeanMn

variable {sys : System}

/-! ### Both-Even Return: core entry conflict construction -/

/-- **Both-Even Return (Mechanism 1).**
    If processor `t` is nonmover at step `a` and mover at step `s`,
    does not fire in `[a, s)`, and both `left t` and `right t` fire
    an even number of times in `[a, s)` (each being binary), then
    there is an entry conflict at `t`.

    This is the most common mechanism for non-consecutive binary:
    in any ternary-phase with M=1, J even, K even, the mover step
    sees the same local context as the first nonmover step. -/
theorem bothEvenReturn_ec
    (gc : GoodCycle sys)
    (t : Fin sys.rs.n)
    -- Steps a (nonmover) and s (mover) with a < s
    (a s : Fin gc.configs.length)
    (halt : a.val < s.val)
    -- t is the mover at step s
    (hs_mover : gc.moverAt s = t)
    -- t is NOT the mover at step a
    (ha_nonmover : gc.moverAt a ≠ t)
    -- t does not fire in [a, s), so its value is preserved
    (ht_nofire : ∀ k : Fin gc.configs.length,
      a.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ t)
    -- left t is binary
    (hbL : sys.rs.m (left t) = 2)
    -- right t is binary
    (hbR : sys.rs.m (right t) = 2)
    -- left t fires an even number of times in [a, s)
    (hJ_even : Even (gc.intervalFireCount (left t) a.val s.val))
    -- right t fires an even number of times in [a, s)
    (hK_even : Even (gc.intervalFireCount (right t) a.val s.val))
    : hasEntryConflict gc := by
  -- The entry conflict witness: steps s (mover) and a (nonmover) at proc t
  refine ⟨s, a, t, hs_mover, ha_nonmover, ?_, ?_, ?_⟩
  -- Goal 1: left-neighbor values match at steps s and a
  · exact (binary_config_eq_of_even_intervalFireCount gc (left t) hbL
      a.val s.val (Nat.le_of_lt halt) s.isLt hJ_even).symm
  -- Goal 2: t's own value matches (it doesn't fire in [a, s))
  · exact (configVal_eq_of_noFire_between gc t a.val s.val
      (Nat.le_of_lt halt) s.isLt ht_nofire).symm
  -- Goal 3: right-neighbor values match at steps s and a
  · exact (binary_config_eq_of_even_intervalFireCount gc (right t) hbR
      a.val s.val (Nat.le_of_lt halt) s.isLt hK_even).symm

/-! ### Helper: interval fire count when no fires occur -/

/-- If processor `p` does not fire at any step in `[a, b)`, then
    `prefixFireCount p a = prefixFireCount p b`. -/
private theorem prefixFireCount_eq_of_noFire
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    {a b : Nat} (hab : a ≤ b) (hb : b ≤ gc.configs.length)
    (hno : ∀ k : Fin gc.configs.length, a ≤ k.val → k.val < b →
      gc.moverAt k ≠ p) :
    gc.prefixFireCount p a = gc.prefixFireCount p b := by
  induction b with
  | zero => simp [show a = 0 from by omega]
  | succ b ih =>
    by_cases hab' : a = b + 1
    · subst hab'; rfl
    · have hab2 : a ≤ b := by omega
      have hb' : b ≤ gc.configs.length := by omega
      have ih' := ih hab2 hb' (fun k h1 h2 => hno k h1 (by omega))
      rw [gc.prefixFireCount_succ]
      have hb_lt : b < gc.configs.length := by omega
      have hfire : gc.fireIndicator p b = 0 := by
        rw [gc.fireIndicator_of_lt p hb_lt]
        have hne : gc.moverAt ⟨b, hb_lt⟩ ≠ p := by
          apply hno ⟨b, hb_lt⟩
          · exact hab2
          · exact Nat.lt_succ_self b
        split_ifs with h
        · exact absurd h hne
        · rfl
      rw [hfire, Nat.add_zero]
      exact ih'

/-- If processor `p` does not fire at any step in `[a, b)`, then
    its interval fire count is zero. -/
theorem intervalFireCount_eq_zero_of_noFire
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    {a b : Nat} (hab : a ≤ b) (hb : b ≤ gc.configs.length)
    (hno : ∀ k : Fin gc.configs.length, a ≤ k.val → k.val < b →
      gc.moverAt k ≠ p) :
    gc.intervalFireCount p a b = 0 := by
  unfold GoodCycle.intervalFireCount
  have := prefixFireCount_eq_of_noFire gc p hab hb hno
  omega

/-- If `p` does not fire at any step in `[a, b)` and
    `gc.intervalFireCount p c b` is even for `c ≤ a`,
    then `gc.intervalFireCount p c a` is also even. -/
theorem intervalFireCount_even_restrict
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    {c a b : Nat} (_hca : c ≤ a) (hab : a ≤ b) (hb : b ≤ gc.configs.length)
    (hno : ∀ k : Fin gc.configs.length, a ≤ k.val → k.val < b →
      gc.moverAt k ≠ p)
    (heven : Even (gc.intervalFireCount p c b)) :
    Even (gc.intervalFireCount p c a) := by
  have hpfc_eq := prefixFireCount_eq_of_noFire gc p hab hb hno
  -- intervalFireCount p c b = pfc(b) - pfc(c) = pfc(a) - pfc(c) = intervalFireCount p c a
  unfold GoodCycle.intervalFireCount at heven ⊢
  rw [← hpfc_eq] at heven
  exact heven

/-! ### Binary dichotomy helper -/

/-- In `Fin n` with `n = 2`, if `a ≠ b` then every element equals `a` or `b`. -/
private theorem fin_binary_dichotomy {n : Nat} (hn : n = 2)
    (a b : Fin n) (hab : a ≠ b) (c : Fin n) : c = a ∨ c = b := by
  subst hn
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  -- a.val, b.val, c.val ∈ {0, 1}
  interval_cases a.val <;> interval_cases b.val <;> interval_cases c.val
    <;> simp_all [Fin.ext_iff] <;> omega

/-! ### Mechanism 2: Toggle-FR (one-sided ≥2, other side zero) -/

/-- **Toggle-FR (Mechanism 2).**
    In a ternary phase where `t` has value `k`:
    - `bR = right t` doesn't fire in `[a₁, s]` (so its value is constant);
    - `bL = left t` fires at two steps `a₁ < a₂` where `bL` has distinct
      values, producing two nonmover contexts at `t` that cover both binary
      values of `bL`;
    - `t` fires at step `s > a₂` and doesn't fire in `[a₁, s)`.

    Since `bL` is binary, `t`'s mover context at `s` must match one of the
    two nonmover contexts → entry conflict.

    This covers phases with J ≥ 2 (bL fires ≥ 2 times) and K = 0 (bR
    doesn't fire), for any M ≥ 1. -/
theorem toggleFR_ec
    (gc : GoodCycle sys)
    (t : Fin sys.rs.n)
    -- Three steps: two nonmover steps a₁ < a₂ and mover step s > a₂
    (a₁ a₂ s : Fin gc.configs.length)
    (h12 : a₁.val < a₂.val) (h2s : a₂.val < s.val)
    -- t is the mover at step s
    (hs_mover : gc.moverAt s = t)
    -- t is NOT the mover at steps a₁, a₂ (it's nonmover there)
    (ha₁_nonmover : gc.moverAt a₁ ≠ t)
    (ha₂_nonmover : gc.moverAt a₂ ≠ t)
    -- t does not fire in [a₁, s), so its value is preserved
    (ht_nofire : ∀ k : Fin gc.configs.length,
      a₁.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ t)
    -- left t is binary
    (hbL : sys.rs.m (left t) = 2)
    -- right t is binary (unused in proof but documents the setup)
    (_hbR : sys.rs.m (right t) = 2)
    -- right t does not fire in [a₁, s), so its value is constant
    (hR_nofire : ∀ k : Fin gc.configs.length,
      a₁.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ right t)
    -- bL has DISTINCT values at a₁ and a₂ (covers both binary values)
    (hL_diff : (gc.configs.get a₁) (left t) ≠ (gc.configs.get a₂) (left t))
    : hasEntryConflict gc := by
  -- (A) t's value is the same at a₁, a₂, and s (t doesn't fire in [a₁, s))
  have ht_a₁ : (gc.configs.get a₁) t = (gc.configs.get s) t :=
    configVal_eq_of_noFire_between gc t a₁.val s.val (by omega) s.isLt ht_nofire
  have ht_a₂ : (gc.configs.get a₂) t = (gc.configs.get s) t :=
    configVal_eq_of_noFire_between gc t a₂.val s.val (by omega) s.isLt
      (fun k hk1 hk2 => ht_nofire k (by omega) hk2)
  -- (B) right t's value is the same at a₁, a₂, and s (right t doesn't fire)
  have hR_a₁ : (gc.configs.get a₁) (right t) = (gc.configs.get s) (right t) :=
    configVal_eq_of_noFire_between gc (right t) a₁.val s.val (by omega) s.isLt hR_nofire
  have hR_a₂ : (gc.configs.get a₂) (right t) = (gc.configs.get s) (right t) :=
    configVal_eq_of_noFire_between gc (right t) a₂.val s.val (by omega) s.isLt
      (fun k hk1 hk2 => hR_nofire k (by omega) hk2)
  -- (C) Binary dichotomy: bL's value at s equals bL's value at a₁ or a₂
  have hL_dichotomy :
      (gc.configs.get s) (left t) = (gc.configs.get a₁) (left t) ∨
      (gc.configs.get s) (left t) = (gc.configs.get a₂) (left t) :=
    fin_binary_dichotomy hbL
      ((gc.configs.get a₁) (left t)) ((gc.configs.get a₂) (left t))
      hL_diff ((gc.configs.get s) (left t))
  -- (D) Construct the entry conflict
  rcases hL_dichotomy with hL_eq_a₁ | hL_eq_a₂
  · -- Mover context at s matches nonmover context at a₁
    exact ⟨s, a₁, t, hs_mover, ha₁_nonmover, hL_eq_a₁, ht_a₁.symm, hR_a₁.symm⟩
  · -- Mover context at s matches nonmover context at a₂
    exact ⟨s, a₂, t, hs_mover, ha₂_nonmover, hL_eq_a₂, ht_a₂.symm, hR_a₂.symm⟩

/-! ### Mechanism 3: Zero-Side EC (M=1, one-sided ≥2, other zero) -/

/-- **Zero-Side EC (Mechanism 3).**
    Same core argument as Toggle-FR but stated for the common case M = 1:
    - `bR = right t` doesn't fire at all (K = 0);
    - `bL = left t` fires at two steps `a₁ < a₂` with distinct `bL` values;
    - `t` fires exactly once at step `s` and doesn't fire in `[a₁, s)`.

    Since `bL` is binary, `t`'s mover context must match one of the two
    nonmover contexts → entry conflict.

    The hypotheses are identical to `toggleFR_ec`.  This is provided as a
    separate entry point for clarity: Mechanism 3 is Toggle-FR specialized
    to M = 1 phases, which is the most common single-firing scenario. -/
theorem zeroSide_ec
    (gc : GoodCycle sys)
    (t : Fin sys.rs.n)
    -- Three steps: two nonmover steps a₁ < a₂ and mover step s > a₂
    (a₁ a₂ s : Fin gc.configs.length)
    (h12 : a₁.val < a₂.val) (h2s : a₂.val < s.val)
    -- t is the mover at step s
    (hs_mover : gc.moverAt s = t)
    -- t is NOT the mover at steps a₁, a₂
    (ha₁_nonmover : gc.moverAt a₁ ≠ t)
    (ha₂_nonmover : gc.moverAt a₂ ≠ t)
    -- t does not fire in [a₁, s)
    (ht_nofire : ∀ k : Fin gc.configs.length,
      a₁.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ t)
    -- left t is binary
    (hbL : sys.rs.m (left t) = 2)
    -- right t is binary
    (hbR : sys.rs.m (right t) = 2)
    -- right t does not fire in [a₁, s)
    (hR_nofire : ∀ k : Fin gc.configs.length,
      a₁.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ right t)
    -- bL has DISTINCT values at a₁ and a₂
    (hL_diff : (gc.configs.get a₁) (left t) ≠ (gc.configs.get a₂) (left t))
    : hasEntryConflict gc :=
  toggleFR_ec gc t a₁ a₂ s h12 h2s hs_mover ha₁_nonmover ha₂_nonmover
    ht_nofire hbL hbR hR_nofire hL_diff

/-! ### Symmetric variants (right-side active, left-side zero) -/

/-- **Toggle-FR symmetric variant.**
    Same as `toggleFR_ec` but with left/right swapped: `bL = left t` is
    constant (doesn't fire) and `bR = right t` fires with two distinct
    values at nonmover steps. -/
theorem toggleFR_ec_symm
    (gc : GoodCycle sys)
    (t : Fin sys.rs.n)
    (a₁ a₂ s : Fin gc.configs.length)
    (h12 : a₁.val < a₂.val) (h2s : a₂.val < s.val)
    (hs_mover : gc.moverAt s = t)
    (ha₁_nonmover : gc.moverAt a₁ ≠ t)
    (ha₂_nonmover : gc.moverAt a₂ ≠ t)
    (ht_nofire : ∀ k : Fin gc.configs.length,
      a₁.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ t)
    -- left t is binary (unused in proof but documents the setup)
    (_hbL : sys.rs.m (left t) = 2)
    -- right t is binary
    (hbR : sys.rs.m (right t) = 2)
    -- LEFT t does not fire in [a₁, s) (constant)
    (hL_nofire : ∀ k : Fin gc.configs.length,
      a₁.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ left t)
    -- bR has DISTINCT values at a₁ and a₂
    (hR_diff : (gc.configs.get a₁) (right t) ≠ (gc.configs.get a₂) (right t))
    : hasEntryConflict gc := by
  -- Same structure as toggleFR_ec with L/R swapped
  have ht_a₁ : (gc.configs.get a₁) t = (gc.configs.get s) t :=
    configVal_eq_of_noFire_between gc t a₁.val s.val (by omega) s.isLt ht_nofire
  have ht_a₂ : (gc.configs.get a₂) t = (gc.configs.get s) t :=
    configVal_eq_of_noFire_between gc t a₂.val s.val (by omega) s.isLt
      (fun k hk1 hk2 => ht_nofire k (by omega) hk2)
  have hL_a₁ : (gc.configs.get a₁) (left t) = (gc.configs.get s) (left t) :=
    configVal_eq_of_noFire_between gc (left t) a₁.val s.val (by omega) s.isLt hL_nofire
  have hL_a₂ : (gc.configs.get a₂) (left t) = (gc.configs.get s) (left t) :=
    configVal_eq_of_noFire_between gc (left t) a₂.val s.val (by omega) s.isLt
      (fun k hk1 hk2 => hL_nofire k (by omega) hk2)
  have hR_dichotomy :
      (gc.configs.get s) (right t) = (gc.configs.get a₁) (right t) ∨
      (gc.configs.get s) (right t) = (gc.configs.get a₂) (right t) :=
    fin_binary_dichotomy hbR
      ((gc.configs.get a₁) (right t)) ((gc.configs.get a₂) (right t))
      hR_diff ((gc.configs.get s) (right t))
  rcases hR_dichotomy with hR_eq_a₁ | hR_eq_a₂
  · exact ⟨s, a₁, t, hs_mover, ha₁_nonmover, hL_a₁.symm, ht_a₁.symm, hR_eq_a₁⟩
  · exact ⟨s, a₂, t, hs_mover, ha₂_nonmover, hL_a₂.symm, ht_a₂.symm, hR_eq_a₂⟩

/-- **Zero-Side EC symmetric variant.**
    Same as `zeroSide_ec` but with left/right swapped. -/
theorem zeroSide_ec_symm
    (gc : GoodCycle sys)
    (t : Fin sys.rs.n)
    (a₁ a₂ s : Fin gc.configs.length)
    (h12 : a₁.val < a₂.val) (h2s : a₂.val < s.val)
    (hs_mover : gc.moverAt s = t)
    (ha₁_nonmover : gc.moverAt a₁ ≠ t)
    (ha₂_nonmover : gc.moverAt a₂ ≠ t)
    (ht_nofire : ∀ k : Fin gc.configs.length,
      a₁.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ t)
    (hbL : sys.rs.m (left t) = 2)
    (hbR : sys.rs.m (right t) = 2)
    (hL_nofire : ∀ k : Fin gc.configs.length,
      a₁.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ left t)
    (hR_diff : (gc.configs.get a₁) (right t) ≠ (gc.configs.get a₂) (right t))
    : hasEntryConflict gc :=
  toggleFR_ec_symm gc t a₁ a₂ s h12 h2s hs_mover ha₁_nonmover ha₂_nonmover
    ht_nofire hbL hbR hL_nofire hR_diff

/-! ### Mechanism 4: Traversal Return (M=1, singleton fires first in (2,1)/(1,2) phase)

  Setup: ternary t between binary bL and bR. Phase where c[t] = k, M = 1.
  In a (J,K) = (2,1) phase, singleton = bR fires first among {bL, bR}.
  In a (J,K) = (1,2) phase, singleton = bL fires first.

  **Why entry conflict:**
  After the singleton fires first, its value flips to 1−original and stays
  there for the rest of the phase (it only fires once). The pair side then
  fires twice, producing two nonmover contexts at t that cover both binary
  values of the pair side (all with the singleton's flipped value constant).
  When t fires, its mover context has the same constant singleton value and
  some pair value — matching one of the two nonmover contexts by binary
  dichotomy.

  This reduces to Toggle-FR applied to the sub-interval after the singleton
  fires: the singleton plays the role of the "constant side" (doesn't fire
  again), and the pair plays the "active side" (fires twice with distinct
  values at two nonmover steps). -/

/-- **Traversal Return (Mechanism 4), case (J,K) = (2,1).**
    Singleton = bR fires first (at step `a₀`). Then bL fires at two steps
    `a₁ < a₂` with distinct values (both after `a₀`). t fires at step `s > a₂`.
    bR does not fire in `[a₁, s)` (it already fired once at `a₀ < a₁`).
    This is Toggle-FR on the post-singleton sub-interval. -/
theorem traversalReturn_ec
    (gc : GoodCycle sys)
    (t : Fin sys.rs.n)
    -- Four steps: singleton step a₀, two pair steps a₁ < a₂, mover step s
    -- a₀ documents the singleton firing step (a₀ < a₁ ensures singleton fired first)
    (_a₀ : Fin gc.configs.length)
    (a₁ a₂ s : Fin gc.configs.length)
    (_h01 : _a₀.val < a₁.val) (h12 : a₁.val < a₂.val) (h2s : a₂.val < s.val)
    -- t is the mover at step s
    (hs_mover : gc.moverAt s = t)
    -- t is NOT the mover at steps a₁, a₂
    (ha₁_nonmover : gc.moverAt a₁ ≠ t)
    (ha₂_nonmover : gc.moverAt a₂ ≠ t)
    -- t does not fire in [a₁, s)
    (ht_nofire : ∀ k : Fin gc.configs.length,
      a₁.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ t)
    -- left t is binary
    (hbL : sys.rs.m (left t) = 2)
    -- right t is binary
    (hbR : sys.rs.m (right t) = 2)
    -- right t (singleton) does not fire in [a₁, s) — it already fired at a₀
    (hR_nofire : ∀ k : Fin gc.configs.length,
      a₁.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ right t)
    -- bL (pair) has DISTINCT values at a₁ and a₂
    (hL_diff : (gc.configs.get a₁) (left t) ≠ (gc.configs.get a₂) (left t))
    : hasEntryConflict gc :=
  -- Reduces directly to Toggle-FR: bR is constant in [a₁, s), bL active
  toggleFR_ec gc t a₁ a₂ s h12 h2s hs_mover ha₁_nonmover ha₂_nonmover
    ht_nofire hbL hbR hR_nofire hL_diff

/-- **Traversal Return symmetric (Mechanism 4), case (J,K) = (1,2).**
    Singleton = bL fires first (at step `a₀`). Then bR fires at two steps
    `a₁ < a₂` with distinct values (both after `a₀`). t fires at step `s > a₂`.
    bL does not fire in `[a₁, s)` (it already fired once at `a₀ < a₁`).
    This is Toggle-FR symmetric on the post-singleton sub-interval. -/
theorem traversalReturn_ec_symm
    (gc : GoodCycle sys)
    (t : Fin sys.rs.n)
    -- Four steps: singleton step a₀, two pair steps a₁ < a₂, mover step s
    -- a₀ documents the singleton firing step (a₀ < a₁ ensures singleton fired first)
    (_a₀ : Fin gc.configs.length)
    (a₁ a₂ s : Fin gc.configs.length)
    (_h01 : _a₀.val < a₁.val) (h12 : a₁.val < a₂.val) (h2s : a₂.val < s.val)
    -- t is the mover at step s
    (hs_mover : gc.moverAt s = t)
    -- t is NOT the mover at steps a₁, a₂
    (ha₁_nonmover : gc.moverAt a₁ ≠ t)
    (ha₂_nonmover : gc.moverAt a₂ ≠ t)
    -- t does not fire in [a₁, s)
    (ht_nofire : ∀ k : Fin gc.configs.length,
      a₁.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ t)
    -- left t is binary
    (hbL : sys.rs.m (left t) = 2)
    -- right t is binary
    (hbR : sys.rs.m (right t) = 2)
    -- left t (singleton) does not fire in [a₁, s) — it already fired at a₀
    (hL_nofire : ∀ k : Fin gc.configs.length,
      a₁.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ left t)
    -- bR (pair) has DISTINCT values at a₁ and a₂
    (hR_diff : (gc.configs.get a₁) (right t) ≠ (gc.configs.get a₂) (right t))
    : hasEntryConflict gc :=
  -- Reduces directly to Toggle-FR symmetric: bL is constant in [a₁, s), bR active
  toggleFR_ec_symm gc t a₁ a₂ s h12 h2s hs_mover ha₁_nonmover ha₂_nonmover
    ht_nofire hbL hbR hL_nofire hR_diff

end LeanMn
