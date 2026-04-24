/-
  LowerBound/SK/CloudsTheorem.lean — Clouds-form M_n lower bound

  Full-Clouds target: for every good cycle on a sub-M_n multiset,

      (SK gc).Nonempty

  One sink is enough — T1 soundness (`not_converges_of_SK_nonempty`
  in `SinkKernel.lean`) converts nonemptiness to non-convergence,
  which contradicts `valid`. No cycle-length case split. No floor
  count on `|SK|`. The two theorems below differ only in the
  sub-threshold hypothesis, which is dictated by the math: sharp
  M_n is `32·3^(n-4)` at `n ∈ {5..8}` and `4·3^(n-2)` at `n ≥ 9`.

  The value-set upper bound at `L = 2n` and the det invariants
  needed by peel-style forced-closed-slice arguments are proved
  here as Clouds-useful scaffolding.
-/
import LeanMn.LowerBound.SK.SinkKernel
import LeanMn.LowerBound.SK.SlabCountingRing
import LeanMn.LowerBound.SK.HammingTube
-- BinaryCubeProj moved to Attic (replaced by SlabCounting)
import LeanMn.LowerBound.GoodCycleBasics
import LeanMn.LowerBound.FireCountNe

namespace LeanMn.SK

open LeanMn

variable {sys : System}

/-! ## §0. Cycle length

The cycle length of a `GoodCycle` is just the length of its configs
list. This replaces the sorry stub in the prior version of this
file. -/

/-- The cycle length of a `GoodCycle`: the number of distinct
    configurations in the cycle. -/
def cycleLength (gc : GoodCycle sys) : ℕ := gc.configs.length

@[simp] theorem cycleLength_eq (gc : GoodCycle sys) :
    cycleLength gc = gc.configs.length := rfl

theorem cycleLength_pos (gc : GoodCycle sys) : 0 < cycleLength gc := by
  simp [cycleLength]
  cases h : gc.configs with
  | nil => exact (gc.nonempty h).elim
  | cons hd tl => simp

/-! ## §1. Fairness implies positive fire count

From `gc.fair`, every processor has a firing step, so its `fireCount`
is at least 1. This is the first ingredient for the pigeonhole that
pins `fireCount = 2` at `L = 2n`. -/

/-- Every processor has at least one firing step in the cycle. -/
theorem exists_moverAt_eq (gc : GoodCycle sys) (i : Fin sys.rs.n) :
    ∃ k : Fin gc.configs.length, gc.moverAt k = i := by
  obtain ⟨k, j, hpriv, _hstep, hji⟩ := gc.fair i
  refine ⟨k, ?_⟩
  -- j is privileged at config k and j = i, and moverAt k is unique
  have hmov : j = gc.moverAt k := gc.moverAt_unique k j hpriv
  rw [← hji, hmov]

/-- A processor that fires at least once has `fireCount ≥ 1`. -/
theorem fireCount_pos_of_moverAt (gc : GoodCycle sys)
    (i : Fin sys.rs.n) (k : Fin gc.configs.length)
    (hk : gc.moverAt k = i) :
    1 ≤ gc.fireCount i := by
  classical
  -- fireCount = ∑_{j:Fin length} fireIndicator i j.val
  -- At j = k, fireIndicator i k.val = 1 (since moverAt k = i).
  have hk_lt : k.val < gc.configs.length := k.isLt
  have hfire_k : gc.fireIndicator i k.val = 1 := by
    rw [gc.fireIndicator_of_lt i hk_lt]
    simp [hk]
  -- Bound fireCount ≥ fireIndicator at position k.
  unfold GoodCycle.fireCount GoodCycle.prefixFireCount
  have hk_mem : k.val ∈ Finset.range gc.configs.length :=
    Finset.mem_range.mpr hk_lt
  calc 1 = gc.fireIndicator i k.val := hfire_k.symm
    _ ≤ ∑ j ∈ Finset.range gc.configs.length, gc.fireIndicator i j :=
        Finset.single_le_sum (f := gc.fireIndicator i)
          (fun j _ => Nat.zero_le _) hk_mem

/-- Fairness: every processor fires at least once. -/
theorem fireCount_pos_of_fair (gc : GoodCycle sys) (i : Fin sys.rs.n) :
    1 ≤ gc.fireCount i := by
  obtain ⟨k, hk⟩ := exists_moverAt_eq gc i
  exact fireCount_pos_of_moverAt gc i k hk

/-- Every processor fires at least **twice** in a fair simple closed
    cycle. Combines fairness (`fireCount ≥ 1`) with
    `GoodCycle.fireCount_ne_one` (a single fire cannot close the
    cycle: one privileged fire strictly changes the processor's
    value, but cycle closure demands the value return to its start).

    This is the ingredient the P1 proof sketch for Lemma C-weak
    relies on: any "minimum-fire-count" processor in fact has
    `fireCount = 2` exactly at the tight case `L = 2n+2`, so its
    value range has size ≤ 2 and the binary-cube slicing argument
    applies. -/
theorem fireCount_ge_two_of_fair (gc : GoodCycle sys) (i : Fin sys.rs.n) :
    2 ≤ gc.fireCount i := by
  have h1 := fireCount_pos_of_fair gc i
  have hne := GoodCycle.fireCount_ne_one gc i
  omega

/-! ## §2. Pigeonhole: at `L = 2n`, every processor fires exactly twice

With `∑_i fireCount i = L = 2n` and `fireCount_ge_two_of_fair`
giving `fireCount i ≥ 2` universally, the pigeonhole is immediate:
`n` terms each at least `2` summing to exactly `2n` must each equal
`2`. No upper-bound hypothesis needed. -/

/-- **Part 1 of Lemma A** (pinned, no sorry): at `|C| = 2n`, every
    processor fires **exactly** twice. Proof:
    1. `fireCount_ge_two_of_fair`: each `fc i ≥ 2`.
    2. `sum_fireCount`: `∑ fc i = |C| = 2n`.
    3. `n` terms each ≥ 2 summing to exactly `2n` forces each = 2
       (each `(fc i - 2) ≥ 0` and their sum is `2n - 2n = 0`). -/
theorem fireCount_eq_two_at_min_length (gc : GoodCycle sys)
    (hlen : gc.configs.length = 2 * sys.rs.n)
    (i : Fin sys.rs.n) :
    gc.fireCount i = 2 := by
  classical
  -- Deviation sum: ∑ (fc j - 2) = ∑ fc j - 2n = 0, and each ≥ 0.
  have hge : ∀ j : Fin sys.rs.n, 2 ≤ gc.fireCount j :=
    fun j => fireCount_ge_two_of_fair gc j
  have hsum : ∑ j : Fin sys.rs.n, gc.fireCount j = 2 * sys.rs.n := by
    rw [gc.sum_fireCount, hlen]
  -- Bound via sum of `(fc - 2)` = sum - 2·|univ| = 2n - 2n = 0.
  have hdiff_sum : ∑ j : Fin sys.rs.n, (gc.fireCount j - 2) = 0 := by
    have hcard : (Finset.univ : Finset (Fin sys.rs.n)).card = sys.rs.n := by simp
    have h := Finset.sum_tsub_distrib
      (s := (Finset.univ : Finset (Fin sys.rs.n)))
      (f := gc.fireCount) (g := fun _ => 2)
      (fun j _ => hge j)
    rw [h]
    rw [hsum]
    simp [Finset.sum_const, hcard, Nat.mul_comm]
  -- Since each term is ≥ 0 and the sum is 0, each term = 0.
  have hi0 : gc.fireCount i - 2 = 0 := by
    have hmem : i ∈ (Finset.univ : Finset (Fin sys.rs.n)) := Finset.mem_univ i
    have := Finset.sum_eq_zero_iff_of_nonneg
      (s := (Finset.univ : Finset (Fin sys.rs.n)))
      (f := fun j => gc.fireCount j - 2)
      (fun _ _ => Nat.zero_le _)
    rw [this] at hdiff_sum
    exact hdiff_sum i hmem
  have hge_i := hge i
  omega

/-! ## §4. Value set of a processor along the cycle

The set of distinct values processor `p` takes at any configuration
in the cycle. The key claim: at `|C| = 2n`, every `valueSet p` has
at most 2 elements.

The intuition: between two consecutive fires at `p`, the value is
fixed. With exactly 2 fires, the value trajectory is
`v₀ → v₁ → v₀`, so only 2 distinct values appear. -/

/-- The set of distinct values processor `p` takes along the cycle. -/
def valueSet (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    Finset (Fin (sys.rs.m p)) :=
  (Finset.univ : Finset (Fin gc.configs.length)).image
    (fun k => (gc.configs.get k) p)

/-- `fireIndicator` is always 0 or 1. -/
private theorem fireIndicator_le_one' (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (k : Nat) : gc.fireIndicator p k ≤ 1 := by
  unfold GoodCycle.fireIndicator
  split_ifs <;> omega

/-- `prefixFireCount` is monotone nondecreasing. -/
private theorem prefixFireCount_mono (gc : GoodCycle sys)
    (p : Fin sys.rs.n) {x y : Nat} (hxy : x ≤ y) :
    gc.prefixFireCount p x ≤ gc.prefixFireCount p y := by
  induction y, hxy using Nat.le_induction with
  | base => rfl
  | succ n _ ih =>
    rw [gc.prefixFireCount_succ]
    have hi : gc.fireIndicator p n ≤ 1 := fireIndicator_le_one' gc p n
    omega

/-- Same `prefixFireCount` on an interval ⟹ same `stateAfter`: if the prefix
fire counts of `p` at indices `a ≤ b ≤ L` agree, then `p` does not fire on
`[a, b)`, so its state is preserved. -/
private theorem stateAfter_eq_of_prefixFireCount_eq
    (gc : GoodCycle sys) (p : Fin sys.rs.n) {a b : Nat}
    (hab : a ≤ b) (hb : b ≤ gc.configs.length)
    (hpfc : gc.prefixFireCount p a = gc.prefixFireCount p b) :
    gc.stateAfter p a = gc.stateAfter p b := by
  symm
  apply gc.stateAfter_eq_of_no_fire p hab hb
  intro k hka hkb hmov
  -- moverAt k = p ⟹ fireIndicator p k.val = 1, so pfc strictly jumps at k.
  have hfire : gc.fireIndicator p k.val = 1 := by
    rw [gc.fireIndicator_of_lt p k.isLt]; simp [hmov]
  have hstep : gc.prefixFireCount p (k.val + 1) =
      gc.prefixFireCount p k.val + 1 := by
    rw [gc.prefixFireCount_succ, hfire]
  have h1 := prefixFireCount_mono gc p hka
  have h2 := prefixFireCount_mono gc p (show k.val + 1 ≤ b by omega)
  omega

/-- Closure of the cycle: `stateAfter p L = stateAfter p 0`. -/
private theorem stateAfter_length_eq' (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    gc.stateAfter p gc.configs.length = gc.stateAfter p 0 := by
  rw [gc.stateAfter_of_ge p le_rfl, gc.stateAfter_of_lt p gc.configs_length_pos]
  rfl

/-- At `|C| = 2n`, the value set of every processor has at most 2
    elements. **Proof**: by `fireCount_eq_two_at_min_length`, `fc p = 2`,
    so `prefixFireCount p · : [0, L] → {0, 1, 2}`. Two indices with the
    same prefix-fire-count agree under `stateAfter p` (no fires between
    them). Closure identifies prefix 0 with prefix 2 (since
    `stateAfter p L = stateAfter p 0`). So `stateAfter p` takes at most
    2 distinct values along the cycle, and `valueSet` coincides with
    the image of `stateAfter p` on `Fin L`. -/
theorem valueSet_card_le_two_at_min_length (gc : GoodCycle sys)
    (hlen : gc.configs.length = 2 * sys.rs.n)
    (p : Fin sys.rs.n) :
    (valueSet gc p).card ≤ 2 := by
  classical
  set L := gc.configs.length with hLdef
  have hLpos : 0 < L := gc.configs_length_pos
  have hfc : gc.fireCount p = 2 := fireCount_eq_two_at_min_length gc hlen p
  have hfcL : gc.prefixFireCount p L = 2 := hfc
  -- Reference value `v0 = stateAfter p 0`.
  let v0 : Fin (sys.rs.m p) := gc.stateAfter p 0
  -- Existence of a "post-first-fire" index: since `fc p = 2 ≥ 1`, there is
  -- some index whose prefixFireCount is `1`. We pick it to define `v1`.
  have hex : ∃ m : Nat, m ≤ L ∧ gc.prefixFireCount p m = 1 := by
    -- `prefixFireCount p 0 = 0` and `prefixFireCount p L = 2`; monotone and
    -- step increments are ≤ 1, so it hits `1` somewhere.
    -- Find minimal `m` with `prefixFireCount p m ≥ 1`.
    by_contra hnone
    push_neg at hnone
    -- No index has pfc = 1. Show that pfc stays ≤ 0 then jumps to ≥ 2, impossible.
    have hstep : ∀ m, m < L → gc.prefixFireCount p m = 0 →
        gc.prefixFireCount p (m + 1) ≤ 1 := by
      intro m _ h0
      rw [gc.prefixFireCount_succ, h0]
      have : gc.fireIndicator p m ≤ 1 := fireIndicator_le_one' gc p m
      omega
    -- By induction, pfc m ≤ 1 for all m ≤ L. But pfc L = 2. Contradiction.
    have hall : ∀ m, m ≤ L → gc.prefixFireCount p m ≤ 1 := by
      intro m hmL
      induction m with
      | zero => simp [gc.prefixFireCount_zero]
      | succ k ih =>
        have hkL : k ≤ L := Nat.le_of_succ_le hmL
        have hkL' : k < L := by omega
        have ihk := ih hkL
        have hne1 : gc.prefixFireCount p k ≠ 1 := hnone k hkL
        have hk0 : gc.prefixFireCount p k = 0 := by omega
        exact hstep k hkL' hk0
    have := hall L le_rfl
    omega
  obtain ⟨m₁, hm₁L, hm₁pfc⟩ := hex
  let v1 : Fin (sys.rs.m p) := gc.stateAfter p m₁
  -- Every `configs[k].p = stateAfter p k.val` lies in `{v0, v1}`.
  have subset_pair : ∀ k : Fin L,
      (gc.configs.get k) p = v0 ∨ (gc.configs.get k) p = v1 := by
    intro k
    have hkL : k.val < L := k.isLt
    -- (configs.get k) p = stateAfter p k.val
    have heq : (gc.configs.get k) p = gc.stateAfter p k.val := by
      rw [gc.stateAfter_of_lt p hkL]
    rw [heq]
    -- pfc p k.val ∈ {0, 1, 2}: ≤ fireCount p = 2 (monotonicity from k ≤ L).
    have hpfc_le : gc.prefixFireCount p k.val ≤ 2 := by
      have := prefixFireCount_mono gc p (Nat.le_of_lt hkL)
      rw [hfcL] at this; exact this
    interval_cases h : gc.prefixFireCount p k.val
    · -- pfc = 0: equal to stateAfter at 0.
      left
      have := stateAfter_eq_of_prefixFireCount_eq gc p (Nat.zero_le _)
        (Nat.le_of_lt hkL) (by rw [gc.prefixFireCount_zero]; exact h.symm)
      exact this.symm
    · -- pfc = 1: equal to stateAfter at m₁.
      right
      by_cases hle : k.val ≤ m₁
      · exact stateAfter_eq_of_prefixFireCount_eq gc p hle hm₁L
          (by rw [h, hm₁pfc])
      · push_neg at hle
        exact (stateAfter_eq_of_prefixFireCount_eq gc p (Nat.le_of_lt hle)
          (Nat.le_of_lt hkL) (by rw [hm₁pfc, h])).symm
    · -- pfc = 2: equal to stateAfter at L (since pfc L = 2), which equals stateAfter 0.
      left
      have hkL2 := stateAfter_eq_of_prefixFireCount_eq gc p
        (Nat.le_of_lt hkL) (le_refl L) (by rw [h, hfcL])
      rw [hkL2]
      exact stateAfter_length_eq' gc p
  -- `valueSet gc p ⊆ {v0, v1}`, so card ≤ 2.
  have hsub : valueSet gc p ⊆ ({v0, v1} : Finset (Fin (sys.rs.m p))) := by
    intro x hx
    unfold valueSet at hx
    rcases Finset.mem_image.mp hx with ⟨k, _, hkx⟩
    rcases subset_pair k with h0 | h1
    · rw [← hkx, h0]; exact Finset.mem_insert_self _ _
    · rw [← hkx, h1]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  calc (valueSet gc p).card
      ≤ ({v0, v1} : Finset (Fin (sys.rs.m p))).card := Finset.card_le_card hsub
    _ ≤ 2 := by
        have hpair : ({v0, v1} : Finset (Fin (sys.rs.m p))).card ≤ 2 := by
          have : ({v0, v1} : Finset (Fin (sys.rs.m p))).card ≤
              ({v0} : Finset (Fin (sys.rs.m p))).card + 1 := by
            simpa using Finset.card_insert_le v0 {v1}
          simpa using this
        exact hpair

/-! ## §5. Det invariants along the value set

If `detOf` returns `some v` from a context `(l, s, r)`, then each
of `l`, `s`, `r` is an attained value along the cycle at its
respective processor. Consequently, forced neighbors preserve the
"off the cycle's value set" property at any processor `p`:
`c p ∉ valueSet gc p` implies `c' p = c p`, so a bad slice persists
under forced motion. These facts feed the Lemma C forced-closed-slice
arguments. -/

private theorem detOf_eq_some_context_mem_valueSet
    (gc : GoodCycle sys)
    (i : Fin sys.rs.n)
    (l : Fin (sys.rs.m (left i)))
    (s : Fin (sys.rs.m i))
    (r : Fin (sys.rs.m (right i)))
    (v : Fin (sys.rs.m i))
    (hdet : detOf gc i l s r = some v) :
    l ∈ valueSet gc (left i) ∧
      s ∈ valueSet gc i ∧
      r ∈ valueSet gc (right i) := by
  classical
  simp only [detOf] at hdet
  generalize hfind :
      (List.finRange gc.configs.length).find?
        (fun k => (gc.configs.get k (left i) == l) &&
                  (gc.configs.get k i == s) &&
                  (gc.configs.get k (right i) == r)) = found at hdet
  cases found with
  | none =>
      simp at hdet
  | some k =>
    have hmatch := List.find?_some hfind
    simp [Bool.and_eq_true, beq_iff_eq] at hmatch
    obtain ⟨⟨hl, hs⟩, hr⟩ := hmatch
    refine ⟨?_, ?_, ?_⟩
    · unfold valueSet
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hl⟩
    · unfold valueSet
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hs⟩
    · unfold valueSet
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hr⟩

private theorem forcedNeighbor_preserves_off_valueSet
    (gc : GoodCycle sys)
    {c c' : Config sys.rs}
    (hforced : c' ∈ forcedNeighbors (detOf gc) c)
    (p : Fin sys.rs.n)
    (hp : c p ∉ valueSet gc p) :
    c' p = c p := by
  classical
  simp only [forcedNeighbors, List.mem_filterMap] at hforced
  obtain ⟨q, _, hq⟩ := hforced
  simp only [forcedOutput] at hq
  generalize hdet : detOf gc q (c (left q)) (c q) (c (right q)) = dval at hq
  cases dval with
  | none =>
      simp at hq
  | some v =>
      by_cases hsame : v = c q
      · simp [hsame] at hq
      · simp [hsame] at hq
        subst hq
        have hq_ne_p : q ≠ p := by
          intro hqp
          subst hqp
          have hs_mem : c q ∈ valueSet gc q :=
            (detOf_eq_some_context_mem_valueSet gc q
              (c (left q)) (c q) (c (right q)) v hdet).2.1
          exact hp hs_mem
        have hp_ne_q : p ≠ q := by
          intro hpq
          exact hq_ne_p hpq.symm
        simp [applyMove, hp_ne_q]

private theorem forcedNeighbor_keeps_badSlice
    (gc : GoodCycle sys)
    {c c' : Config sys.rs}
    (hforced : c' ∈ forcedNeighbors (detOf gc) c)
    (p : Fin sys.rs.n)
    (hp : c p ∉ valueSet gc p) :
    c' p ∉ valueSet gc p := by
  rw [forcedNeighbor_preserves_off_valueSet gc hforced p hp]
  exact hp

/-! ## §6. SK nonempty — the Clouds statement

Full-Clouds form: `(SK gc).Nonempty` at sub-threshold. This is the
only property the M_n lower bound theorem actually consumes — via
T1 soundness (`SinkKernel.not_converges_of_SK_nonempty`), one sink
is enough to witness non-convergence. No cycle-length case split;
no floor count. The two theorems differ only in the sub-threshold
hypothesis, which is dictated by the math (sharp M_n is regime-
dependent): `32·3^(n-4)` at `n ∈ {5..8}`, `4·3^(n-2)` at `n ≥ 9`. -/

/-- **SK nonempty (small-n regime)**: for every good cycle on a
    multiset with state product strictly less than the sharp
    `M_n = 32·3^(n-4)` at `n ∈ {5, 6, 7, 8}`, `SK(C)` is nonempty.

    The sharp small-n threshold is essential: the weaker
    `< 4·3^(n-2)` form admits valid systems in the gap whose good
    cycles have `SK = ∅`, contradicting the conclusion. -/
theorem sk_nonempty_small_n
    (gc : GoodCycle sys)
    (hsub : stateProduct sys.rs < 32 * 3 ^ (sys.rs.n - 4))
    (hn_lo : 5 ≤ sys.rs.n) (hn_hi : sys.rs.n ≤ 8) :
    (SK gc).Nonempty :=
  -- R4 peel-direct route: reduces to `peelTube_nonempty_small_n`
  -- in `HammingTube.lean`. Sharp threshold matches the hypothesis
  -- directly; no widening. Empirical basis: E13 probe 2026-04-20,
  -- 164 cycles, margin ≥ 8 uniformly.
  sk_nonempty_via_tube_small_n gc hn_lo hn_hi hsub

/-- **SK nonempty (n ≥ 9 regime)**: for every good cycle on a
    multiset with state product strictly less than the sharp
    `M_n = 4·3^(n-2)` at `n ≥ 9`, `SK(C)` is nonempty. -/
theorem sk_nonempty_large_n
    (gc : GoodCycle sys)
    (hsub : stateProduct sys.rs < 4 * 3 ^ (sys.rs.n - 2))
    (hn : 9 ≤ sys.rs.n) :
    (SK gc).Nonempty :=
  sk_nonempty_via_tube_large_n gc hn hsub

end LeanMn.SK
