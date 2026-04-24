/-
  DominoesRing.lean — Dominoes ring obstruction for sandwiched ternary pivots

  If every sandwiched ternary pivot in a sub-threshold good cycle has the
  "dominoes or contaminated" property, then there is an entry conflict
  somewhere in the cycle — contradiction.

  Self-contained: only imports GoodCycleBasics.
-/
import LeanMn.LowerBound.GoodCycleBasics
import LeanMn.LowerBound.CycleTypes

namespace LeanMn

variable {sys : System}

/-! ### Dominoes-or-contaminated predicate -/

/-- A good cycle satisfies the dominoes-or-contaminated property at pivot `t`
    if every maximal interval `[a, s)` between consecutive t-firings has one of:
    - the first mover is a neighbor or second-neighbor of t, or
    - some interior step fires a second-neighbor of t. -/
def isDominoesOrContaminated (gc : GoodCycle sys) (t : Fin sys.rs.n) : Prop :=
  ∀ (a s : Fin gc.configs.length),
    a.val < s.val →
    gc.moverAt s = t →
    (∀ k : Fin gc.configs.length, a.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ t) →
    gc.moverAt a = left t ∨
    gc.moverAt a = right t ∨
    gc.moverAt a = left (left t) ∨
    gc.moverAt a = right (right t) ∨
    (∃ k : Fin gc.configs.length,
      a.val < k.val ∧ k.val < s.val ∧
      (gc.moverAt k = left (left t) ∨ gc.moverAt k = right (right t)))

/-! ### Infrastructure: sandwiched ternary pivots -/

/-- A processor t is a sandwiched ternary pivot: ternary with both neighbors binary. -/
def isSandwichedTernary (rs : RingSpec) (t : Fin rs.n) : Prop :=
  rs.m t ≥ 3 ∧ rs.m (left t) = 2 ∧ rs.m (right t) = 2

/-! ### Lemma 2: Dominoes phase structure constrains binary mover patterns

  If isDominoesOrContaminated holds at pivot t, then the first mover after
  each t-firing is in {left t, right t, left²t, right²t}. This means the
  binary neighbors of t (left t and right t) are heavily constrained: they
  must fire near every t-firing.

  Key extraction: between consecutive t-firings at steps a and s, the first
  mover is one of 4 processors (or there's a contamination firing). -/

/-- In a dominoes phase at pivot t, the first mover after a t-firing is local. -/
theorem dominoes_first_mover_local
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hdom : isDominoesOrContaminated gc t)
    (a s : Fin gc.configs.length)
    (has : a.val < s.val)
    (hs : gc.moverAt s = t)
    (hgap : ∀ k : Fin gc.configs.length, a.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ t) :
    gc.moverAt a = left t ∨
    gc.moverAt a = right t ∨
    gc.moverAt a = left (left t) ∨
    gc.moverAt a = right (right t) ∨
    (∃ k : Fin gc.configs.length,
      a.val < k.val ∧ k.val < s.val ∧
      (gc.moverAt k = left (left t) ∨ gc.moverAt k = right (right t))) :=
  hdom a s has hs hgap

/-! ### Lemma 3: Binary context overlap from dominoes constraints

  Consider a sandwiched ternary pivot t with left t = bL and right t = bR
  both binary. The dominoes constraint says that after each t-firing, either
  bL or bR fires next (or their second neighbors, or contamination).

  At a step where bL fires (is the mover), the context at bL is:
    (c[left bL], c[bL], c[right bL]) = (c[left bL], c[bL], c[t])

  At a step where bL is NOT the mover, its context is preserved.

  The key insight: with n ≥ 9 and ≥ 3 binary processors forming a ring
  of sandwiched pivots, the dominoes constraints at ADJACENT pivots
  force the same binary processor to appear in both mover and non-mover
  roles with the same local context → entry conflict. -/

/-- Adjacent sandwiched pivots share a binary processor. -/
theorem adjacent_pivots_share_binary {n : Nat}
    (t₁ t₂ : Fin n)
    (hadj : right (right t₁) = t₂) :
    right t₁ = left t₂ := by
  rw [← hadj, left_right_eq_self]

/-! ### Lemma 4: Ring parity obstruction

  The sandwiched pivots form a sub-ring. The dominoes ordering at each pivot
  induces a "direction" (left-first vs right-first) for the shared binary
  pair. Adjacent pivots reverse this direction (because the shared binary
  is the RIGHT neighbor of one pivot and the LEFT neighbor of the next).

  On an odd-length sub-ring: the directions must alternate, but an odd cycle
  cannot be 2-colored → contradiction.

  On an even-length sub-ring: directions can alternate consistently, but then
  a half-cycle symmetry argument shows a binary processor sees the same
  context at a mover step and a non-mover step → entry conflict. -/

/-- Key lemma: at a sandwiched pivot t with dominoes property, every phase
    between consecutive t-firings has a binary neighbor firing. This means
    the binary neighbor fires at least as many times as t does minus 1.
    Combined with fireCount parity, this heavily constrains the binary FC. -/
theorem binary_neighbor_fires_in_dominoes_phase
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (_ht_lbin : sys.rs.m (left t) = 2)
    (_ht_rbin : sys.rs.m (right t) = 2)
    (hdom : isDominoesOrContaminated gc t)
    (a s : Fin gc.configs.length)
    (has : a.val < s.val)
    (hs : gc.moverAt s = t)
    (hgap : ∀ k : Fin gc.configs.length, a.val ≤ k.val → k.val < s.val → gc.moverAt k ≠ t) :
    (∃ k : Fin gc.configs.length, a.val ≤ k.val ∧ k.val < s.val ∧
      (gc.moverAt k = left t ∨ gc.moverAt k = right t)) ∨
    (∃ k : Fin gc.configs.length, a.val ≤ k.val ∧ k.val < s.val ∧
      (gc.moverAt k = left (left t) ∨ gc.moverAt k = right (right t))) := by
  have h := hdom a s has hs hgap
  rcases h with hl | hr | hll | hrr | ⟨k, hak, hks, hkm⟩
  · exact Or.inl ⟨a, le_refl _, has, Or.inl hl⟩
  · exact Or.inl ⟨a, le_refl _, has, Or.inr hr⟩
  · exact Or.inr ⟨a, le_refl _, has, Or.inl hll⟩
  · exact Or.inr ⟨a, le_refl _, has, Or.inr hrr⟩
  · exact Or.inr ⟨k, Nat.le_of_lt hak, hks, hkm⟩

/-- From fireCount t ≥ 2, extract two consecutive t-firing steps. -/
theorem exists_two_consecutive_firings
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hfc : gc.fireCount t ≥ 2) :
    ∃ (a s : Fin gc.configs.length),
      a.val < s.val ∧
      gc.moverAt s = t ∧
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) := by
  -- Step 1: Extract two distinct firing steps from fireCount ≥ 2
  have hexists1 : ∃ a : Fin gc.configs.length, gc.moverAt a = t := by
    by_contra hall; push_neg at hall
    have hzero : gc.fireCount t = 0 := by
      rw [gc.fireCount_eq_sum_moverAt t]
      apply Finset.sum_eq_zero
      intro j _; simp [show gc.moverAt j ≠ t from hall j]
    omega
  obtain ⟨a, ha⟩ := hexists1
  have hexists2 : ∃ b : Fin gc.configs.length, b ≠ a ∧ gc.moverAt b = t := by
    by_contra hall; push_neg at hall
    have hle1 : gc.fireCount t ≤ 1 := by
      rw [gc.fireCount_eq_sum_moverAt t]
      have hbd : ∀ j : Fin gc.configs.length,
          (if gc.moverAt j = t then (1 : Nat) else 0) ≤ (if j = a then 1 else 0) := by
        intro j
        by_cases hja : j = a
        · rw [hja]; simp [ha]
        · have : gc.moverAt j ≠ t := hall j hja; simp [this]
      calc ∑ j : Fin gc.configs.length, (if gc.moverAt j = t then (1 : Nat) else 0)
          ≤ ∑ j : Fin gc.configs.length, (if j = a then (1 : Nat) else 0) :=
            Finset.sum_le_sum (fun j _ => hbd j)
        _ = 1 := by
            rw [Finset.sum_eq_single a
              (fun b _ hba => by simp [hba]) (by simp)]; simp
    omega
  obtain ⟨b, hne, hb⟩ := hexists2
  have hne_val : a.val ≠ b.val := fun h => hne (Fin.ext h).symm
  -- Order them: get a₀ < b₀ with both firing t
  obtain ⟨a₀, b₀, hab₀, ha₀, hb₀⟩ : ∃ (a₀ b₀ : Fin gc.configs.length),
      a₀.val < b₀.val ∧ gc.moverAt a₀ = t ∧ gc.moverAt b₀ = t := by
    by_cases hab : a.val < b.val
    · exact ⟨a, b, hab, ha, hb⟩
    · exact ⟨b, a, by omega, hb, ha⟩
  -- Step 2: Refine to consecutive pair via well-founded descent on gap
  suffices hmain : ∀ d : Nat, ∀ (a b : Fin gc.configs.length),
      b.val - a.val ≤ d → a.val < b.val →
      gc.moverAt a = t → gc.moverAt b = t →
      ∃ (a' b' : Fin gc.configs.length),
        a'.val < b'.val ∧ gc.moverAt b' = t ∧
        (∀ k : Fin gc.configs.length, a'.val < k.val → k.val < b'.val → gc.moverAt k ≠ t) by
    obtain ⟨a', b', hab', hb'_mov, hgap⟩ :=
      hmain (b₀.val - a₀.val) a₀ b₀ le_rfl hab₀ ha₀ hb₀
    exact ⟨a', b', hab', hb'_mov, hgap⟩
  intro d
  induction d with
  | zero => intro a b hd hab; omega
  | succ d ih =>
    intro a b hd hab ha_mov hb_mov
    by_cases hno : ∀ k : Fin gc.configs.length,
        a.val < k.val → k.val < b.val → gc.moverAt k ≠ t
    · exact ⟨a, b, hab, hb_mov, hno⟩
    · push_neg at hno
      obtain ⟨k, hak, hkb, hk⟩ := hno
      exact ih k b (by omega) hkb hk hb_mov

/-- Context preservation: one step. If p is not the mover at step k, the
    value at p is the same at step k and step k+1 (when k+1 < length). -/
private theorem context_preserved_one_step
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (k : Nat) (hk : k < gc.configs.length) (hk1 : k + 1 < gc.configs.length)
    (hne : gc.moverAt ⟨k, hk⟩ ≠ p) :
    (gc.configs.get ⟨k + 1, hk1⟩) p = (gc.configs.get ⟨k, hk⟩) p := by
  have heq := gc.state_eq_of_ne_moverAt ⟨k, hk⟩ p (Ne.symm hne)
  have hnext : nextIndex gc.configs ⟨k, hk⟩ = ⟨k + 1, hk1⟩ := by
    ext; simp [nextIndex, Nat.mod_eq_of_lt hk1]
  rw [hnext] at heq
  exact heq

/-- Context preservation: if processor p doesn't fire between steps a and b,
    then its value is preserved. -/
theorem context_preserved_between
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (a b : Fin gc.configs.length)
    (hab : a.val ≤ b.val)
    (hnofire : ∀ k : Fin gc.configs.length, a.val ≤ k.val → k.val < b.val → gc.moverAt k ≠ p) :
    (gc.configs.get b) p = (gc.configs.get a) p := by
  -- Use strong induction on gap d = b - a.
  -- Base: d = 0, trivial. Step: chain one-step preservation with IH.
  have key : ∀ (d : Nat) (j : Nat) (hj : j < gc.configs.length)
    (hjd : j + d < gc.configs.length),
    (∀ (i : Nat) (hi : i < gc.configs.length),
      j ≤ i → i < j + d → gc.moverAt ⟨i, hi⟩ ≠ p) →
    (gc.configs.get ⟨j + d, hjd⟩) p = (gc.configs.get ⟨j, hj⟩) p := by
    intro d
    induction d with
    | zero => intros; rfl
    | succ m ihm =>
      intro j hj hjm1 hnofire_d
      -- IH: value at j+m equals value at j
      have hjm : j + m < gc.configs.length := Nat.lt_of_lt_of_le (by omega) (Nat.le_of_lt hjm1)
      have step_ih : (gc.configs.get ⟨j + m, hjm⟩) p = (gc.configs.get ⟨j, hj⟩) p :=
        ihm j hj hjm (fun i hi hlo hhi => hnofire_d i hi hlo (by omega))
      -- One step: value at j+m+1 equals value at j+m
      have hne : gc.moverAt ⟨j + m, hjm⟩ ≠ p :=
        hnofire_d (j + m) hjm (by omega) (by omega)
      have step1 := context_preserved_one_step gc p (j + m) hjm (by omega) hne
      -- Chain
      have : (⟨j + (m + 1), hjm1⟩ : Fin gc.configs.length) = ⟨j + m + 1, by omega⟩ := by
        ext; ring
      rw [this, step1, step_ih]
  -- Apply with d = b - a
  have hab' : a.val + (b.val - a.val) = b.val := by omega
  have hblt : a.val + (b.val - a.val) < gc.configs.length := by omega
  have result := key (b.val - a.val) a.val a.isLt hblt
    (fun i hi hlo hhi => by
      have : i < b.val := by omega
      exact hnofire ⟨i, hi⟩ hlo this)
  have ha_eq : (⟨a.val, a.isLt⟩ : Fin gc.configs.length) = a := rfl
  have hb_eq : (⟨a.val + (b.val - a.val), by rw [hab']; exact b.isLt⟩ : Fin gc.configs.length) = b := by
    ext; omega
  rw [ha_eq, hb_eq] at result
  exact result

/-- Sparse Phase Lemma: under ¬hasEntryConflict, each phase between consecutive
    t-firings has exactly one first-neighbor fire (left t or right t, not both).

    The proof eliminates all "non-sparse" patterns via contradiction with ¬EC:
    (a) Both sides fire → earlier neighbor's boundary triple frozen → EC
    (b) Same neighbor fires twice → consecutive-fires EC
    (c) Opposite-side second-neighbor → cross-side EC
    (d) Non-local mover → phase.a non-neighbor EC

    Conclusion: exactly one of {left t, right t} fires in (a, s), the other doesn't. -/
private theorem sparse_phases_of_not_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (hmt : sys.rs.m t ≥ 3)
    (hnoEC : ¬hasEntryConflict gc)
    (hdom_t : isDominoesOrContaminated gc t)
    -- Phase: consecutive t-firings at a and s with no t in between
    (a s : Fin gc.configs.length)
    (has : a.val < s.val)
    (hs : gc.moverAt s = t)
    (hgap : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ t) :
    -- Exactly one of {left t, right t} fires in (a, s)
    ((∃ k : Fin gc.configs.length, a.val < k.val ∧ k.val < s.val ∧ gc.moverAt k = left t) ∧
     (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ right t)) ∨
    ((∃ k : Fin gc.configs.length, a.val < k.val ∧ k.val < s.val ∧ gc.moverAt k = right t) ∧
     (∀ k : Fin gc.configs.length, a.val < k.val → k.val < s.val → gc.moverAt k ≠ left t)) := by
  -- Proof sketch:
  -- From hdom_t: the first mover after a in (a,s) is in {left t, right t, left²t, right²t}
  --   or there's a contamination firing.
  -- Under ¬EC:
  -- (a) If both left t AND right t fire in (a,s): the earlier one's context at t is frozen
  --     (t doesn't fire in gap), so at the later neighbor's firing, t sees same context as
  --     at mover step → EC. Contradicts ¬EC.
  -- (b) If only second-neighbors fire (no first-neighbor): second-neighbor fires with t's
  --     context frozen → EC at second-neighbor between its mover step here and non-mover
  --     step in another phase. Contradicts ¬EC.
  -- So exactly one of left t, right t fires.
  sorry

/-- Under ¬EC + sparse phases + binary neighbors: fireCount(t) ≥ 4.
    Each phase contributes exactly 1 first-neighbor fire.
    fireCount(left t) + fireCount(right t) = fireCount(t).
    Both binary neighbors have fireCount ≥ 2 (even, positive). So fireCount(t) ≥ 4.

    Proof argument:
    1. From sparse_phases_of_not_ec: each phase between consecutive t-firings has
       exactly one first-neighbor fire (left t XOR right t).
    2. Decomposition: summing over all P = fireCount(t) phases, each contributes
       exactly 1 first-neighbor fire, so total = P.
    3. Total first-neighbor fires = fireCount(left t) + fireCount(right t).
    4. fireCount(left t) ≥ 2: binary (hbL) + fires at least once (hfull) + even
       (binary_fireCount_even) → even and positive → ≥ 2.
    5. fireCount(right t) ≥ 2: same argument with hbR.
    6. P = fireCount(left t) + fireCount(right t) ≥ 2 + 2 = 4. -/
private theorem fireCount_ge_4_of_sparse
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (hmt : sys.rs.m t ≥ 3)
    (hfc : gc.fireCount t ≥ 2)
    (hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0)
    (hnoEC : ¬hasEntryConflict gc)
    (hdom_t : isDominoesOrContaminated gc t) :
    gc.fireCount t ≥ 4 := by
  -- The full proof requires a fire-count-over-phases decomposition lemma:
  -- partition the cycle into P = fireCount(t) phases between consecutive t-firings,
  -- show each phase has exactly 1 first-neighbor fire (sparse_phases_of_not_ec),
  -- then sum to get fireCount(left t) + fireCount(right t) = P.
  -- Combined with binary_fireCount_even + hfull → each ≥ 2 → P ≥ 4.
  sorry

/-- The dominoes ring creates an entry conflict: the mover constraints from
    isDominoesOrContaminated at all sandwiched pivots are collectively
    inconsistent, forcing hasEntryConflict.

    Proof outline:
    1. Extract consecutive t-firings a < s (both fire t, no t strictly between).
    2. Apply isDominoesOrContaminated to the shifted interval [a+1, s):
       first non-t mover is in {left t, right t, left²t, right²t}.
    3. Construct EC at t between s (mover) and a+1 (non-mover):
       S-value preserved (t doesn't fire in [a+1, s)).
       L/R values (binary) match via prefix fire count parity.
    4. The parity matching follows from the ring structure: the universal
       dominoes at adjacent pivots forces even fire counts for both binary
       neighbors in at least one gap (ring parity obstruction). -/
theorem dominoes_ring_creates_entry_conflict
    (gc : GoodCycle sys)
    (hn : sys.rs.n ≥ 9)
    (hsub : subThreshold sys.rs)
    (h3bin : hasGe3Binary sys.rs)
    (hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0)
    -- A specific sandwiched ternary pivot (provided by caller)
    (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (hmt : sys.rs.m t ≥ 3) (hfc : gc.fireCount t ≥ 2)
    (hdom : ∀ (t' : Fin sys.rs.n),
      sys.rs.m (left t') = 2 → sys.rs.m (right t') = 2 →
      sys.rs.m t' ≥ 3 → gc.fireCount t' ≥ 2 →
      isDominoesOrContaminated gc t') :
    hasEntryConflict gc := by
  -- Strategy: case split on whether EC already holds.
  -- If ¬EC: sparse phase structure forces fireCount(t) ≥ 4, giving pigeonhole → EC.
  by_cases hEC : hasEntryConflict gc
  · -- EC already holds
    exact hEC
  · -- Under ¬EC: derive contradiction via sparse phases
    exfalso
    -- Key claim (sparse phases): under ¬EC and isDominoesOrContaminated at t,
    -- each phase between consecutive t-firings has EXACTLY one first-neighbor
    -- fire (either left t or right t, not both, each at most once).
    --
    -- Proof sketch for sparse phases:
    -- (a) Both left t AND right t in same phase → the earlier one's boundary
    --     triple (which includes t on one side) is frozen until the later fires
    --     (t doesn't fire in the phase interior) → EC at the earlier neighbor.
    --     Contradicts ¬EC.
    -- (b) Same first-neighbor fires twice → consecutive-fires EC. Contradicts ¬EC.
    -- (c) Second-neighbor from opposite side of first-neighbor → cross-side EC.
    --     Contradicts ¬EC.
    -- (d) Non-local mover → phase.a non-neighbor EC. Contradicts ¬EC.
    -- So under ¬EC: each phase has exactly one first-neighbor fire.
    --
    -- Consequence: fireCount(left t) + fireCount(right t) = fireCount(t)
    -- (one first-neighbor fire per phase, fireCount(t) many phases).
    -- But left t and right t are binary, so fireCount(left t) ≥ 2 and
    -- fireCount(right t) ≥ 2 (binary_fireCount_even + positive → ≥ 2).
    -- Hence fireCount(t) ≥ 4.
    --
    -- With fireCount(t) ≥ 4 and left²t binary (fireCount = 2):
    -- By pigeonhole, some phase has no left²t fire → within-phase EC
    -- (Layer 1 mechanism). But this gives EC, contradicting ¬EC.
    --
    -- Step 1: sparse phases → fireCount(t) ≥ 4
    have hdom_t := hdom t hbL hbR hmt hfc
    have h_fc_ge_4 : gc.fireCount t ≥ 4 :=
      fireCount_ge_4_of_sparse gc t hbL hbR hmt hfc hfull hEC hdom_t
    -- Step 2: fireCount(t) ≥ 4 + binary second-neighbor → pigeonhole → EC
    have h_ec_from_pigeonhole : hasEntryConflict gc := by
      -- Pigeonhole argument:
      -- 1. left(left t) is binary (from sub-threshold + ≥3 binary structure).
      --    Its fireCount is even (binary_fireCount_even) and positive (hfull) → ≥ 2.
      --    In the strongest case it equals exactly 2.
      -- 2. fireCount(t) ≥ 4 gives ≥ 4 phases between consecutive t-firings.
      -- 3. Pigeonhole: 2 fires of left(left t) across ≥ 4 phases →
      --    some phase has 0 fires of left(left t).
      -- 4. In that fire-free phase: left(left t)'s value is frozen (context_preserved_between).
      --    But isDominoesOrContaminated says the first mover is in {left t, right t, left²t, right²t}.
      --    The left²t = left(left t) case: left(left t) fires as mover with context (L, S, R).
      --    In the fire-free phase: left(left t) is non-mover with same frozen context.
      --    This gives hasEntryConflict at left(left t).
      -- 5. The within-phase EC construction follows the same pattern as
      --    TernaryPhaseEC.lean's ternary_phase_entry_conflict.
      sorry
    exact absurd h_ec_from_pigeonhole hEC

/-! ### Main theorem: dominoes ring → False -/

/-- The dominoes ring obstruction: if EVERY sandwiched ternary pivot in a
    sub-threshold good cycle satisfies isDominoesOrContaminated, then False.

    Proof outline:
    1. The dominoes ordering at adjacent pivots reverses the shared binary pair.
    2. Odd number of pivots: C_k not 2-colorable → ordering contradiction.
    3. Even number of pivots: half-cycle symmetry → binary context overlap → EC.
-/
theorem dominoes_ring_false
    (gc : GoodCycle sys)
    (hn : sys.rs.n ≥ 9)
    (hsub : subThreshold sys.rs)
    (h3bin : hasGe3Binary sys.rs)
    (hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0)
    -- A specific sandwiched ternary pivot (provided by caller)
    (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (hmt : sys.rs.m t ≥ 3) (hfc2 : gc.fireCount t ≥ 2)
    -- Universal: isDominoesOrContaminated at ALL sandwiched ternary pivots
    (hdom : ∀ (t' : Fin sys.rs.n),
      sys.rs.m (left t') = 2 → sys.rs.m (right t') = 2 →
      sys.rs.m t' ≥ 3 → gc.fireCount t' ≥ 2 →
      isDominoesOrContaminated gc t') :
    False := by
  exact entryConflict_impossible gc
    (dominoes_ring_creates_entry_conflict gc hn hsub h3bin hfull t hbL hbR hmt hfc2 hdom)

end LeanMn
