/-
  Result1.lean — Both sandwich-Ts can't simultaneously be no-stay

  Lean port of Result 1 from
  `docs/lean_docs/lb_campaign_2026-04-12/linear_stay_lemma_attempt_2026-04-14.md`
  §Result 1. Used by the L4d rotation-invariance closure
  (`docs/lean_docs/lb_campaign_2026-04-12/rotation_invariance_l4d_2026-04-14.md`).

  The proof is a 9-step slot-count saturation:
    1. Slot count (6 × 2 = 12 slot instances)
    2. Binary contribution bound (6 × 2 = 12 max)
    3. Saturation: tight 12 = 12 forces every binary fire to have
       both neighbors at sandwich-T
    4. Proc 0 → [1, 0, 1] pattern
    5. Proc 4 → [3, 4, 3] pattern
    6. Proc 0 cluster [1, 0, 1, 0, 1]: consumes fc[0] = 2, fc[1] = 3
    7. Proc 4 cluster [3, 4, 3, 4, 3]: consumes fc[4] = 2, fc[3] = 3
    8. Proc 2 bridging analysis: fc[2] = 2 fires must satisfy
       walker-adjacency on `{1, 3}`
    9. Walker trap at the last near-cluster position (proc 2)
       can't reach outer procs `{5, ..., n-1}` — contradiction.

  This file currently provides the statement and decomposition skeleton.
  The individual sub-proofs are structured sorries to be filled in
  subsequent sessions.
-/
import LeanMn.LowerBound.CycleTypes
import LeanMn.LowerBound.Proof.Rotation
import LeanMn.LowerBound.Proof.ZeroWinding
import LeanMn.LowerBound.EntryConflict.NestedFirings

namespace LeanMn

variable {sys : System}

/-- A **linear stay** at proc `i` is a pair of consecutive `i`-fires
    at indices `k` and `k + 1` (both in `[0, L - 1)`). -/
def GoodCycle.hasLinearStayAt (gc : GoodCycle sys) (i : Fin sys.rs.n) : Prop :=
  ∃ k : Fin gc.configs.length, ∃ hlt : k.val + 1 < gc.configs.length,
    gc.moverAt k = i ∧
    gc.moverAt ⟨k.val + 1, hlt⟩ = i

/-- A **wrap stay** at proc `i` is `moverAt(L - 1) = moverAt(0) = i`. -/
def GoodCycle.hasWrapStayAt (gc : GoodCycle sys) (i : Fin sys.rs.n) : Prop :=
  gc.moverAt ⟨gc.configs.length - 1,
    Nat.sub_lt gc.configs_length_pos Nat.one_pos⟩ = i ∧
  gc.moverAt ⟨0, gc.configs_length_pos⟩ = i

/-- A **cyclic stay** at proc `i` is either a linear stay or a wrap stay. -/
def GoodCycle.hasStayAt (gc : GoodCycle sys) (i : Fin sys.rs.n) : Prop :=
  gc.hasLinearStayAt i ∨ gc.hasWrapStayAt i

/-- **Pivot family multiset shape**: positions 0, 2, 4 are binary (m=2)
    and positions 1, 3, 5, ..., n-1 are ternary (m=3). This is
    `ms = (2, 3, 2, 3, 2, 3, 3, ..., 3)` from the analytical doc. -/
def isPivotFamily (rs : RingSpec) : Prop :=
  rs.n ≥ 9 ∧
  (∀ p : Fin rs.n, p.val ∈ ({0, 2, 4} : Finset Nat) → rs.m p = 2) ∧
  (∀ p : Fin rs.n, p.val ∉ ({0, 2, 4} : Finset Nat) → rs.m p = 3)

/-- **No-stay characterization (linear part).**

    If `gc` has no linear stay at `i`, then for every index `k` with
    `k + 1 < L`, `moverAt k = i` implies `moverAt (k + 1) ≠ i`. -/
theorem not_hasLinearStayAt_iff (gc : GoodCycle sys) (i : Fin sys.rs.n) :
    ¬ gc.hasLinearStayAt i ↔
    ∀ k : Fin gc.configs.length, ∀ hlt : k.val + 1 < gc.configs.length,
      gc.moverAt k = i → gc.moverAt ⟨k.val + 1, hlt⟩ ≠ i := by
  constructor
  · intro h k hlt hk hk1
    exact h ⟨k, hlt, hk, hk1⟩
  · intro h ⟨k, hlt, hk, hk1⟩
    exact h k hlt hk hk1

/-- **No-stay characterization (wrap part).**

    If `gc` has no wrap stay at `i`, then `moverAt(L - 1) ≠ i` or
    `moverAt(0) ≠ i`. -/
theorem not_hasWrapStayAt_iff (gc : GoodCycle sys) (i : Fin sys.rs.n) :
    ¬ gc.hasWrapStayAt i ↔
    (gc.moverAt ⟨gc.configs.length - 1,
      Nat.sub_lt gc.configs_length_pos Nat.one_pos⟩ ≠ i ∨
     gc.moverAt ⟨0, gc.configs_length_pos⟩ ≠ i) := by
  unfold GoodCycle.hasWrapStayAt
  exact not_and_or

/-- If walker locality + target set intersect to a singleton, the
    post-step mover is pinned. This is the atomic step used in
    Result 1's Step 4 (proc 0 → [1, 0, 1]) and Step 5 (proc 4 →
    [3, 4, 3]).

    Specifically: if `moverAt k = p` and `moverAt (k+1) ∈ S` (as
    a hypothesis of the slot-count saturation), then
    `moverAt (k+1) ∈ {left p, p, right p} ∩ S`. If that intersection
    is `{q}`, the conclusion pins `moverAt (k+1) = q`. -/
theorem next_mover_pin_of_local_inter
    (_gc : GoodCycle sys) (_k : Fin _gc.configs.length) (p q : Fin sys.rs.n)
    (_hp : _gc.moverAt _k = p)
    (_hin : _gc.moverAt (nextIndex _gc.configs _k) = q)
    (hq_local : q = left p ∨ q = p ∨ q = right p) :
    q ∈ ({left p, p, right p} : Finset (Fin sys.rs.n)) := by
  rcases hq_local with h | h | h <;> rw [h] <;> simp

/-- **No-linear-stay forces gap ≥ 2 between consecutive fires.**

    If `gc` has no linear stay at `i`, then any two fires of `i` at
    linearly-ordered indices `f₀ < f₁` must have `f₁.val ≥ f₀.val + 2`.

    This is the core structural consequence of the no-linear-stay
    hypothesis and is used repeatedly in Result 1's Steps 1-8. -/
theorem gap_ge_2_of_no_linear_stay
    (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (f₀ f₁ : Fin gc.configs.length)
    (hlt : f₀.val < f₁.val)
    (hf₀ : gc.moverAt f₀ = i) (hf₁ : gc.moverAt f₁ = i)
    (hnls : ¬ gc.hasLinearStayAt i) :
    f₀.val + 2 ≤ f₁.val := by
  by_contra h
  push_neg at h
  -- h : f₁.val < f₀.val + 2, combined with f₀.val < f₁.val gives f₁.val = f₀.val + 1
  have hf₁_eq : f₁.val = f₀.val + 1 := by omega
  -- Construct a linear stay at f₀
  apply hnls
  have hf₀_succ_lt : f₀.val + 1 < gc.configs.length := hf₁_eq ▸ f₁.isLt
  refine ⟨f₀, hf₀_succ_lt, hf₀, ?_⟩
  -- Goal: moverAt ⟨f₀.val + 1, hf₀_succ_lt⟩ = i
  -- f₁ has value f₀.val + 1, so ⟨f₀.val + 1, _⟩ = f₁
  have hfin_eq : (⟨f₀.val + 1, hf₀_succ_lt⟩ : Fin gc.configs.length) = f₁ := by
    apply Fin.ext
    exact hf₁_eq.symm
  rw [hfin_eq]
  exact hf₁

/-- **Three fires + no linear stay → all three have strict gaps.**

    With `fc i = 3` and no linear stay at `i`, the three fires
    `f₀ < f₁ < f₂` extracted from `exists_three_firing_steps_of_ge3`
    satisfy `f₁ ≥ f₀ + 2` AND `f₂ ≥ f₁ + 2`. This gives the minimum
    spread needed for the slot-count argument. -/
theorem three_fires_gap_structure
    (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (hfc : gc.fireCount i = 3)
    (hnls : ¬ gc.hasLinearStayAt i) :
    ∃ (f₀ f₁ f₂ : Fin gc.configs.length),
      f₀.val + 2 ≤ f₁.val ∧ f₁.val + 2 ≤ f₂.val ∧
      gc.moverAt f₀ = i ∧ gc.moverAt f₁ = i ∧ gc.moverAt f₂ = i := by
  have hfc_ge : gc.fireCount i ≥ 3 := by omega
  obtain ⟨f₀, f₁, f₂, h01, h12, hm0, hm1, hm2⟩ :=
    exists_three_firing_steps_of_ge3 gc i hfc_ge
  refine ⟨f₀, f₁, f₂, ?_, ?_, hm0, hm1, hm2⟩
  · exact gap_ge_2_of_no_linear_stay gc i f₀ f₁ h01 hm0 hm1 hnls
  · exact gap_ge_2_of_no_linear_stay gc i f₁ f₂ h12 hm1 hm2 hnls

/-! ### Pivot family walker locality helpers

    These lemmas express the specific walker-neighbor constraints for
    the pivot family multiset `(2, 3, 2, 3, 2, 3, ..., 3)`. They are
    used in Result 1's Steps 4, 5, and 9. -/

/-- **`left 0 = n - 1` when `n ≥ 2`.** -/
private lemma left_zero_eq (n : Nat) (hn : 2 ≤ n) :
    (left (⟨0, by omega⟩ : Fin n)).val = n - 1 := by
  show (0 + n - 1) % n = n - 1
  rw [Nat.zero_add]
  exact Nat.mod_eq_of_lt (Nat.sub_lt (by omega) Nat.one_pos)

/-- **`right 0 = 1` when `n ≥ 2`.** -/
private lemma right_zero_eq (n : Nat) (hn : 2 ≤ n) :
    (right (⟨0, by omega⟩ : Fin n)).val = 1 := by
  show (0 + 1) % n = 1
  exact Nat.mod_eq_of_lt (by omega)

/-- **`left 2 = 1` when `n ≥ 3`.** -/
private lemma left_two_eq (n : Nat) (hn : 3 ≤ n) :
    (left (⟨2, by omega⟩ : Fin n)).val = 1 := by
  show (2 + n - 1) % n = 1
  have : 2 + n - 1 = n + 1 := by omega
  rw [this, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- **`right 2 = 3` when `n ≥ 4`.** -/
private lemma right_two_eq (n : Nat) (hn : 4 ≤ n) :
    (right (⟨2, by omega⟩ : Fin n)).val = 3 := by
  show (2 + 1) % n = 3
  exact Nat.mod_eq_of_lt (by omega)

/-- **`left 4 = 3` when `n ≥ 5`.** -/
private lemma left_four_eq (n : Nat) (hn : 5 ≤ n) :
    (left (⟨4, by omega⟩ : Fin n)).val = 3 := by
  show (4 + n - 1) % n = 3
  have : 4 + n - 1 = n + 3 := by omega
  rw [this, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- **`right 4 = 5` when `n ≥ 6`.** -/
private lemma right_four_eq (n : Nat) (hn : 6 ≤ n) :
    (right (⟨4, by omega⟩ : Fin n)).val = 5 := by
  show (4 + 1) % n = 5
  exact Nat.mod_eq_of_lt (by omega)

/-! ### Slot-count infrastructure (Result 1 Step 1)

    The core of Result 1's slot-count argument: define the set of
    "slot instances" for sandwich-T `i` (pairs of (i-fire, side)),
    show its cardinality equals `2 * fireCount i`, and express each
    instance as a cyclic-predecessor or cyclic-successor index. -/

/-- **Slot instance set for proc `i`.** Each element is a pair
    `(k, b)` where `k` is a proc-`i` fire index and `b : Bool`
    selects pred (`false`) or succ (`true`) side. -/
private noncomputable def slotInstances (gc : GoodCycle sys) (i : Fin sys.rs.n) :
    Finset (Fin gc.configs.length × Bool) :=
  (Finset.univ.filter (fun k : Fin gc.configs.length => gc.moverAt k = i))
    ×ˢ (Finset.univ : Finset Bool)

/-- **Cardinality of the slot instance set.**

    For a fire count `fireCount i = n`, the slot set has `2 * n`
    elements. In particular, for min-CL sandwich-Ts with `fc = 3`,
    there are 6 slot instances per sandwich-T. -/
private lemma slotInstances_card (gc : GoodCycle sys) (i : Fin sys.rs.n) :
    (slotInstances gc i).card = 2 * gc.fireCount i := by
  unfold slotInstances
  rw [Finset.card_product]
  have hbool : (Finset.univ : Finset Bool).card = 2 := by decide
  rw [hbool]
  have hcount : gc.fireCount i =
      (Finset.univ.filter (fun k : Fin gc.configs.length => gc.moverAt k = i)).card := by
    rw [gc.fireCount_eq_sum_moverAt i]
    rw [Finset.card_filter]
  rw [← hcount]
  ring

/-- **Slot instance count for `fc = 3`.** -/
private lemma slotInstances_card_fc3 (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (hfc : gc.fireCount i = 3) :
    (slotInstances gc i).card = 6 := by
  rw [slotInstances_card, hfc]

/-- **Slot instances at distinct procs are disjoint.** -/
private lemma slotInstances_disjoint (gc : GoodCycle sys) (i j : Fin sys.rs.n)
    (hne : i ≠ j) :
    Disjoint (slotInstances gc i) (slotInstances gc j) := by
  unfold slotInstances
  rw [Finset.disjoint_left]
  intro ⟨k, b⟩ hi hj
  rw [Finset.mem_product, Finset.mem_filter] at hi hj
  exact hne (hi.1.2.symm.trans hj.1.2)

/-- **Combined slot instances across both sandwich-Ts = 12 elements.** -/
private lemma slotInstances_union_card_two_fc3
    (gc : GoodCycle sys) (i j : Fin sys.rs.n) (hne : i ≠ j)
    (hfci : gc.fireCount i = 3) (hfcj : gc.fireCount j = 3) :
    (slotInstances gc i ∪ slotInstances gc j).card = 12 := by
  rw [Finset.card_union_of_disjoint (slotInstances_disjoint gc i j hne)]
  rw [slotInstances_card_fc3 gc i hfci, slotInstances_card_fc3 gc j hfcj]

/-- **Total fire count of pivot-family binaries is 6.** -/
private lemma pivot_binary_total_fireCount (gc : GoodCycle sys)
    (hpivot : isPivotFamily sys.rs)
    (hfc0 : gc.fireCount ⟨0, by have := hpivot.1; omega⟩ = 2)
    (hfc2 : gc.fireCount ⟨2, by have := hpivot.1; omega⟩ = 2)
    (hfc4 : gc.fireCount ⟨4, by have := hpivot.1; omega⟩ = 2) :
    gc.fireCount ⟨0, by have := hpivot.1; omega⟩
    + gc.fireCount ⟨2, by have := hpivot.1; omega⟩
    + gc.fireCount ⟨4, by have := hpivot.1; omega⟩ = 6 := by
  rw [hfc0, hfc2, hfc4]

/-- **Binary fire positions (pivot family).** The set of positions
    where the cycle fires one of the three binaries `{0, 2, 4}`. -/
private noncomputable def pivotBinaryFirePositions
    (gc : GoodCycle sys) (hpivot : isPivotFamily sys.rs) :
    Finset (Fin gc.configs.length) :=
  have hn_lb : 5 ≤ sys.rs.n := by have := hpivot.1; omega
  Finset.univ.filter (fun k : Fin gc.configs.length =>
    gc.moverAt k = ⟨0, by omega⟩ ∨
    gc.moverAt k = ⟨2, by omega⟩ ∨
    gc.moverAt k = ⟨4, by omega⟩)

/-- **Per-proc fire position count equals `fireCount`.** The number
    of indices `k` with `moverAt k = p` is exactly `fireCount p`. -/
private lemma firePositions_card_eq_fireCount
    (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    (Finset.univ.filter (fun k : Fin gc.configs.length => gc.moverAt k = p)).card
      = gc.fireCount p := by
  rw [gc.fireCount_eq_sum_moverAt]
  rw [Finset.card_filter]

/-- **Distinct-proc fire position sets are disjoint.** -/
private lemma firePositions_disjoint_of_ne
    (gc : GoodCycle sys) (p q : Fin sys.rs.n) (hne : p ≠ q) :
    Disjoint
      (Finset.univ.filter (fun k : Fin gc.configs.length => gc.moverAt k = p))
      (Finset.univ.filter (fun k : Fin gc.configs.length => gc.moverAt k = q)) := by
  rw [Finset.disjoint_left]
  intro k hp hq
  rw [Finset.mem_filter] at hp hq
  exact hne (hp.2.symm.trans hq.2)

/-- **The pivot binary fire positions set has cardinality 6** under
    the pivot family fire count hypotheses. Used as the "6 binary
    fires" input to Step 2's counting argument. -/
private lemma pivotBinaryFirePositions_card
    (gc : GoodCycle sys) (hpivot : isPivotFamily sys.rs)
    (hfc0 : gc.fireCount ⟨0, by have := hpivot.1; omega⟩ = 2)
    (hfc2 : gc.fireCount ⟨2, by have := hpivot.1; omega⟩ = 2)
    (hfc4 : gc.fireCount ⟨4, by have := hpivot.1; omega⟩ = 2) :
    (pivotBinaryFirePositions gc hpivot).card = 6 := by
  have hn := hpivot.1
  set p0 : Fin sys.rs.n := ⟨0, by omega⟩ with hp0_def
  set p2 : Fin sys.rs.n := ⟨2, by omega⟩ with hp2_def
  set p4 : Fin sys.rs.n := ⟨4, by omega⟩ with hp4_def
  set S0 := Finset.univ.filter (fun k : Fin gc.configs.length => gc.moverAt k = p0)
    with hS0_def
  set S2 := Finset.univ.filter (fun k : Fin gc.configs.length => gc.moverAt k = p2)
    with hS2_def
  set S4 := Finset.univ.filter (fun k : Fin gc.configs.length => gc.moverAt k = p4)
    with hS4_def
  have hne02 : p0 ≠ p2 := by
    intro h; have := congrArg Fin.val h; simp [hp0_def, hp2_def] at this
  have hne04 : p0 ≠ p4 := by
    intro h; have := congrArg Fin.val h; simp [hp0_def, hp4_def] at this
  have hne24 : p2 ≠ p4 := by
    intro h; have := congrArg Fin.val h; simp [hp2_def, hp4_def] at this
  have hdisj02 : Disjoint S0 S2 := firePositions_disjoint_of_ne gc p0 p2 hne02
  have hdisj04 : Disjoint S0 S4 := firePositions_disjoint_of_ne gc p0 p4 hne04
  have hdisj24 : Disjoint S2 S4 := firePositions_disjoint_of_ne gc p2 p4 hne24
  have hcard0 : S0.card = 2 := by
    rw [hS0_def, firePositions_card_eq_fireCount]; exact hfc0
  have hcard2 : S2.card = 2 := by
    rw [hS2_def, firePositions_card_eq_fireCount]; exact hfc2
  have hcard4 : S4.card = 2 := by
    rw [hS4_def, firePositions_card_eq_fireCount]; exact hfc4
  -- Express pivotBinaryFirePositions as S0 ∪ S2 ∪ S4 via filter_or.
  unfold pivotBinaryFirePositions
  rw [Finset.filter_or, Finset.filter_or]
  -- filter_or gives S0 ∪ (S2 ∪ S4). Compute the card.
  have hdisj_0_24 : Disjoint S0 (S2 ∪ S4) := by
    rw [Finset.disjoint_union_right]
    exact ⟨hdisj02, hdisj04⟩
  rw [Finset.card_union_of_disjoint hdisj_0_24]
  rw [Finset.card_union_of_disjoint hdisj24]
  rw [hcard0, hcard2, hcard4]

/-! ### Cyclic pred/succ helpers

    Used for the slot-count argument in Result 1's Steps 1-3. -/

/-- **Cyclic predecessor index.** For `k : Fin L` with `L > 0`,
    `cyclicPred k = (k - 1) mod L`. -/
private def cyclicPred {L : Nat} (hL : 0 < L) (k : Fin L) : Fin L :=
  ⟨(k.val + L - 1) % L, Nat.mod_lt _ hL⟩

/-- **Cyclic successor index.** -/
private def cyclicSucc {L : Nat} (hL : 0 < L) (k : Fin L) : Fin L :=
  ⟨(k.val + 1) % L, Nat.mod_lt _ hL⟩

/-- **Linear pred is cyclic pred when not at position 0.** -/
private lemma cyclicPred_of_pos {L : Nat} (hL : 0 < L) (k : Fin L)
    (hk : 0 < k.val) :
    (cyclicPred hL k).val = k.val - 1 := by
  unfold cyclicPred
  show (k.val + L - 1) % L = k.val - 1
  have heq : k.val + L - 1 = (k.val - 1) + L := by omega
  rw [heq, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- **Linear succ is cyclic succ when not at position L-1.** -/
private lemma cyclicSucc_of_lt {L : Nat} (hL : 0 < L) (k : Fin L)
    (hk : k.val + 1 < L) :
    (cyclicSucc hL k).val = k.val + 1 := by
  unfold cyclicSucc
  exact Nat.mod_eq_of_lt hk

/-- **Cyclic pred wraps to L-1 from position 0.** -/
private lemma cyclicPred_of_zero {L : Nat} (hL : 0 < L)
    (k : Fin L) (hk : k.val = 0) :
    (cyclicPred hL k).val = L - 1 := by
  unfold cyclicPred
  show (k.val + L - 1) % L = L - 1
  rw [hk, Nat.zero_add]
  exact Nat.mod_eq_of_lt (Nat.sub_lt hL Nat.one_pos)

/-- **Cyclic succ wraps to 0 from position L-1.** -/
private lemma cyclicSucc_of_last {L : Nat} (hL : 0 < L)
    (k : Fin L) (hk : k.val + 1 = L) :
    (cyclicSucc hL k).val = 0 := by
  unfold cyclicSucc
  show (k.val + 1) % L = 0
  rw [hk]
  exact Nat.mod_self L

/-- **`cyclicSucc` equals `nextIndex`.** The GoodCycle's `nextIndex`
    is definitionally `cyclicSucc` for the same length. -/
private lemma cyclicSucc_eq_nextIndex {L : Nat} (hL : 0 < L)
    (xs : List α) (hlen : xs.length = L) (k : Fin L) :
    (cyclicSucc hL k).val = (nextIndex xs ⟨k.val, hlen ▸ k.isLt⟩).val := by
  unfold cyclicSucc nextIndex
  show (k.val + 1) % L = (k.val + 1) % xs.length
  rw [hlen]

/-- **Iterating `cyclicSucc` m times lands at `(k.val + m) % L`.** -/
private lemma cyclicSucc_iterate_val {L : Nat} (hL : 0 < L) (k : Fin L) (m : Nat) :
    ((cyclicSucc hL)^[m] k).val = (k.val + m) % L := by
  induction m with
  | zero =>
    show k.val = (k.val + 0) % L
    rw [Nat.add_zero]; exact (Nat.mod_eq_of_lt k.isLt).symm
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    show (((cyclicSucc hL)^[m] k).val + 1) % L = (k.val + (m + 1)) % L
    rw [ih, Nat.mod_add_mod]
    rfl

/-- **Orbit coverage.** From any start point, iterating `cyclicSucc`
    covers every element of `Fin L`. -/
private lemma cyclicSucc_orbit_univ {L : Nat} (hL : 0 < L) (k k' : Fin L) :
    ∃ m : Nat, (cyclicSucc hL)^[m] k = k' := by
  refine ⟨(k'.val + L - k.val) % L, ?_⟩
  apply Fin.ext
  rw [cyclicSucc_iterate_val]
  have hk := k.isLt
  have hk' := k'.isLt
  by_cases hlt : k'.val < k.val
  · have h1 : k'.val + L - k.val < L := by omega
    rw [Nat.mod_eq_of_lt h1]
    have h2 : k.val + (k'.val + L - k.val) = k'.val + L := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hk']
  · push_neg at hlt
    have h1 : k'.val + L - k.val = (k'.val - k.val) + L := by omega
    rw [h1, Nat.add_mod_right]
    have h2 : k'.val - k.val < L := by omega
    rw [Nat.mod_eq_of_lt h2]
    have h3 : k.val + (k'.val - k.val) = k'.val := by omega
    rw [h3, Nat.mod_eq_of_lt hk']

/-- **Result 1 Step 9 building block — `proc 2`'s next mover is in `{1, 2, 3}`.**

    By `next_mover_is_local`, the mover one step after a proc-2 fire
    must be in `{left 2, 2, right 2} = {1, 2, 3}`. In particular, it
    is NOT in the outer region `{5, 6, ..., n-1}`, which is the
    walker-trap observation at the end of Result 1. -/
theorem next_mover_after_proc2_not_outer
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (k : Fin gc.configs.length)
    (h2 : gc.moverAt k = ⟨2, by omega⟩) :
    (gc.moverAt (nextIndex gc.configs k)).val ≤ 3 := by
  have hloc := gc.next_mover_is_local k
  simp only at hloc
  rw [h2] at hloc
  rcases hloc with hleft | hself | hright
  · -- next = left 2 = 1
    rw [hleft]
    have := left_two_eq sys.rs.n (by omega)
    omega
  · -- next = 2
    rw [hself]; simp
  · -- next = right 2 = 3
    rw [hright]
    have := right_two_eq sys.rs.n (by omega)
    omega

/-- **Result 1 Step 4 building block — proc 0 walker-locality ∩ {1, 3} = {1}.**

    Given a proc-0 fire at index `k`, the next mover is in
    `{left 0, 0, right 0} = {n-1, 0, 1}`. If the saturation hypothesis
    gives "next mover ∈ {1, 3}", the only matching option is `1`. -/
theorem next_mover_after_proc0_in_1_3
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (k : Fin gc.configs.length)
    (h0 : gc.moverAt k = ⟨0, by omega⟩)
    (hsat : (gc.moverAt (nextIndex gc.configs k)).val = 1 ∨
            (gc.moverAt (nextIndex gc.configs k)).val = 3) :
    (gc.moverAt (nextIndex gc.configs k)).val = 1 := by
  have hloc := gc.next_mover_is_local k
  simp only at hloc
  rw [h0] at hloc
  rcases hloc with hleft | hself | hright
  · -- next = left 0 = n - 1 ≥ 8, not 1 or 3
    exfalso
    have hval := left_zero_eq sys.rs.n (by omega)
    rw [hleft, hval] at hsat
    omega
  · -- next = 0, not 1 or 3
    exfalso
    rw [hself] at hsat
    simp at hsat
  · -- next = right 0 = 1 ✓
    rw [hright]
    exact right_zero_eq sys.rs.n (by omega)

/-- **Result 1 Step 5 building block — proc 4 walker-locality ∩ {1, 3} = {3}.**

    Given a proc-4 fire at index `k`, the next mover is in
    `{left 4, 4, right 4} = {3, 4, 5}`. Only `3` matches `{1, 3}`. -/
theorem next_mover_after_proc4_in_1_3
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (k : Fin gc.configs.length)
    (h4 : gc.moverAt k = ⟨4, by omega⟩)
    (hsat : (gc.moverAt (nextIndex gc.configs k)).val = 1 ∨
            (gc.moverAt (nextIndex gc.configs k)).val = 3) :
    (gc.moverAt (nextIndex gc.configs k)).val = 3 := by
  have hloc := gc.next_mover_is_local k
  simp only at hloc
  rw [h4] at hloc
  rcases hloc with hleft | hself | hright
  · -- next = left 4 = 3 ✓
    rw [hleft]
    exact left_four_eq sys.rs.n (by omega)
  · -- next = 4, not 1 or 3
    exfalso
    rw [hself] at hsat
    simp at hsat
  · -- next = right 4 = 5, not 1 or 3
    exfalso
    have hval := right_four_eq sys.rs.n (by omega)
    rw [hright, hval] at hsat
    omega

/-- **Stay conversion under rotation (wrap → linear).**

    A wrap stay at `i` in `gc` corresponds to a linear stay at `i`
    in the cycle rotated by `L - 1`. This is the key mathematical
    observation for Case B/C of the L4d rotation-invariance closure:
    we can always rotate a wrap stay into a linear stay, at which
    point standard linear-witness reasoning applies.

    Note: this lemma just exhibits a rotation that witnesses the
    linear-stay form; the downstream L4d closure consumes it via
    the full rotation invariance bundle. -/
theorem exists_rotation_linearizing_wrap_stay
    (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (hL : 2 ≤ gc.configs.length)
    (hwrap : gc.hasWrapStayAt i) :
    ∃ gc' : GoodCycle sys,
      gc'.configs.length = gc.configs.length ∧
      gc'.hasLinearStayAt i := by
  set L := gc.configs.length with hL_def
  have hLpos : 0 < L := gc.configs_length_pos
  obtain ⟨gc', _hmem, hlen, hmover⟩ :=
    exists_rotated_goodCycle gc (L - 1)
  refine ⟨gc', hlen, ?_⟩
  have hL'_ge_2 : 2 ≤ gc'.configs.length := by rw [hlen]; exact hL
  have h0_lt : (0 : Nat) < gc'.configs.length := by omega
  have h1_lt : (1 : Nat) < gc'.configs.length := by omega
  have h01_lt : (0 : Nat) + 1 < gc'.configs.length := by omega
  refine ⟨⟨0, h0_lt⟩, h01_lt, ?_, ?_⟩
  · -- gc'.moverAt ⟨0, _⟩ = i
    rw [hmover ⟨0, h0_lt⟩]
    have hmod : (0 + (L - 1)) % L = L - 1 := by
      rw [Nat.zero_add]
      exact Nat.mod_eq_of_lt (Nat.sub_lt hLpos Nat.one_pos)
    have hfin_eq :
        (⟨(0 + (L - 1)) % L, Nat.mod_lt _ hLpos⟩ : Fin L)
          = ⟨L - 1, Nat.sub_lt hLpos Nat.one_pos⟩ :=
      Fin.ext hmod
    rw [hfin_eq]
    exact hwrap.1
  · -- gc'.moverAt ⟨1, _⟩ = i  (the `⟨k.val + 1, _⟩ = ⟨0 + 1, _⟩ = ⟨1, _⟩`)
    show gc'.moverAt ⟨0 + 1, h01_lt⟩ = i
    rw [hmover ⟨0 + 1, h01_lt⟩]
    have hmod : ((0 + 1) + (L - 1)) % L = 0 := by
      have heq : (0 + 1) + (L - 1) = L := by omega
      rw [heq]
      exact Nat.mod_self L
    have hfin_eq :
        (⟨((0 + 1) + (L - 1)) % L, Nat.mod_lt _ hLpos⟩ : Fin L)
          = ⟨0, hLpos⟩ :=
      Fin.ext hmod
    rw [hfin_eq]
    exact hwrap.2

/-- **Two distinct procs can't simultaneously have wrap stays.**

    A wrap stay at proc `i` pins `moverAt(0) = i`. Two distinct procs
    can't both equal `moverAt(0)`, so the conjunction is absurd.

    This is the trivial "Case D" of the L4d rotation-invariance closure
    (see `rotation_invariance_l4d_2026-04-14.md`). -/
theorem wrap_stay_disjoint (gc : GoodCycle sys) (i j : Fin sys.rs.n)
    (hne : i ≠ j) (hi : gc.hasWrapStayAt i) (hj : gc.hasWrapStayAt j) :
    False := by
  have h0i : gc.moverAt ⟨0, gc.configs_length_pos⟩ = i := hi.2
  have h0j : gc.moverAt ⟨0, gc.configs_length_pos⟩ = j := hj.2
  exact hne (h0i.symm.trans h0j)

/-! ### Result 1 Step 3 — saturation via cyclicSucc bijection

    The elegant form of Step 3: `cyclicSucc` is a bijection on Fin L,
    and under no-stay at both sandwich-Ts, it restricts to a
    bijection between the 6 sandwich-T fire positions and the 6
    binary fire positions. This immediately gives: for every binary
    fire q, both `cyclicPred q` and `cyclicSucc q` have their
    `moverAt` in {1, 3}. -/

/-- **Sandwich-T fire positions (pivot family).** -/
private noncomputable def pivotSandwichTFirePositions
    (gc : GoodCycle sys) (hpivot : isPivotFamily sys.rs) :
    Finset (Fin gc.configs.length) :=
  have hn_lb : 5 ≤ sys.rs.n := by have := hpivot.1; omega
  Finset.univ.filter (fun k : Fin gc.configs.length =>
    gc.moverAt k = ⟨1, by omega⟩ ∨
    gc.moverAt k = ⟨3, by omega⟩)

/-- **Sandwich-T fire positions count equals 6** under fc[1] = fc[3] = 3. -/
private lemma pivotSandwichTFirePositions_card
    (gc : GoodCycle sys) (hpivot : isPivotFamily sys.rs)
    (hfc1 : gc.fireCount ⟨1, by have := hpivot.1; omega⟩ = 3)
    (hfc3 : gc.fireCount ⟨3, by have := hpivot.1; omega⟩ = 3) :
    (pivotSandwichTFirePositions gc hpivot).card = 6 := by
  have hn := hpivot.1
  set p1 : Fin sys.rs.n := ⟨1, by omega⟩ with hp1_def
  set p3 : Fin sys.rs.n := ⟨3, by omega⟩ with hp3_def
  set S1 := Finset.univ.filter (fun k : Fin gc.configs.length => gc.moverAt k = p1)
    with hS1_def
  set S3 := Finset.univ.filter (fun k : Fin gc.configs.length => gc.moverAt k = p3)
    with hS3_def
  have hne13 : p1 ≠ p3 := by
    intro h; have := congrArg Fin.val h; simp [hp1_def, hp3_def] at this
  have hdisj : Disjoint S1 S3 := firePositions_disjoint_of_ne gc p1 p3 hne13
  have hcard1 : S1.card = 3 := by
    rw [hS1_def, firePositions_card_eq_fireCount]; exact hfc1
  have hcard3 : S3.card = 3 := by
    rw [hS3_def, firePositions_card_eq_fireCount]; exact hfc3
  unfold pivotSandwichTFirePositions
  rw [Finset.filter_or]
  rw [Finset.card_union_of_disjoint hdisj]
  rw [hcard1, hcard3]

/-- **`cyclicPred` is a left-inverse of `cyclicSucc`.** -/
private lemma cyclicPred_cyclicSucc {L : Nat} (hL : 0 < L) (k : Fin L) :
    cyclicPred hL (cyclicSucc hL k) = k := by
  apply Fin.ext
  unfold cyclicPred cyclicSucc
  show ((k.val + 1) % L + L - 1) % L = k.val
  by_cases hk : k.val + 1 < L
  · rw [Nat.mod_eq_of_lt hk]
    have h1 : k.val + 1 + L - 1 = k.val + L := by omega
    rw [h1, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt k.isLt
  · push_neg at hk
    have hkeq : k.val + 1 = L := by omega
    have h1 : (k.val + 1) % L = 0 := by rw [hkeq]; exact Nat.mod_self L
    rw [h1]
    have h2 : (0 + L - 1) % L = L - 1 := by
      have : 0 + L - 1 = L - 1 := by omega
      rw [this, Nat.mod_eq_of_lt (Nat.sub_lt hL Nat.one_pos)]
    rw [h2]
    omega

/-- **`cyclicSucc` is a left-inverse of `cyclicPred`.** -/
private lemma cyclicSucc_cyclicPred {L : Nat} (hL : 0 < L) (k : Fin L) :
    cyclicSucc hL (cyclicPred hL k) = k := by
  apply Fin.ext
  unfold cyclicPred cyclicSucc
  show ((k.val + L - 1) % L + 1) % L = k.val
  by_cases hk : 0 < k.val
  · have h1 : (k.val + L - 1) % L = k.val - 1 := by
      have heq : k.val + L - 1 = (k.val - 1) + L := by omega
      rw [heq, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have h2 : k.val - 1 + 1 = k.val := by omega
    rw [h2, Nat.mod_eq_of_lt k.isLt]
  · push_neg at hk
    have hkeq : k.val = 0 := by omega
    have h1 : (k.val + L - 1) % L = L - 1 := by
      rw [hkeq, Nat.zero_add]
      exact Nat.mod_eq_of_lt (Nat.sub_lt hL Nat.one_pos)
    rw [h1]
    have h2 : (L - 1 + 1) % L = 0 := by
      have : L - 1 + 1 = L := by omega
      rw [this]; exact Nat.mod_self L
    rw [h2, hkeq]

/-- **`cyclicSucc` is injective.** -/
private lemma cyclicSucc_injective {L : Nat} (hL : 0 < L) :
    Function.Injective (cyclicSucc hL) := by
  intro k₁ k₂ heq
  have h1 := cyclicPred_cyclicSucc hL k₁
  have h2 := cyclicPred_cyclicSucc hL k₂
  rw [← h1, ← h2, heq]

/-- **`cyclicPred` is injective.** -/
private lemma cyclicPred_injective {L : Nat} (hL : 0 < L) :
    Function.Injective (cyclicPred hL) := by
  intro k₁ k₂ heq
  have h1 := cyclicSucc_cyclicPred hL k₁
  have h2 := cyclicSucc_cyclicPred hL k₂
  rw [← h1, ← h2, heq]

/-- **`cyclicSucc` at sandwich-T under no-stay ≠ same sandwich-T.** -/
private lemma cyclicSucc_ne_self_of_no_stay
    (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (hns : ¬ gc.hasStayAt i)
    (k : Fin gc.configs.length) (hk : gc.moverAt k = i) :
    gc.moverAt (cyclicSucc gc.configs_length_pos k) ≠ i := by
  intro hsucc
  apply hns
  have hLpos : 0 < gc.configs.length := gc.configs_length_pos
  by_cases hlt : k.val + 1 < gc.configs.length
  · left
    refine ⟨k, hlt, hk, ?_⟩
    have hval : (⟨k.val + 1, hlt⟩ : Fin gc.configs.length).val
                = (cyclicSucc hLpos k).val := by
      symm; exact cyclicSucc_of_lt hLpos k hlt
    have heq : (⟨k.val + 1, hlt⟩ : Fin gc.configs.length) = cyclicSucc hLpos k :=
      Fin.ext hval
    rw [heq]; exact hsucc
  · right
    push_neg at hlt
    have hkval : k.val = gc.configs.length - 1 := by omega
    have hkeq :
        k = ⟨gc.configs.length - 1, Nat.sub_lt hLpos Nat.one_pos⟩ :=
      Fin.ext hkval
    have hsval : (cyclicSucc hLpos k).val = 0 :=
      cyclicSucc_of_last hLpos k (by omega)
    have hseq : cyclicSucc hLpos k = ⟨0, hLpos⟩ := Fin.ext hsval
    refine ⟨?_, ?_⟩
    · show gc.moverAt ⟨gc.configs.length - 1, _⟩ = i
      rw [← hkeq]; exact hk
    · show gc.moverAt ⟨0, _⟩ = i
      rw [← hseq]; exact hsucc

/-- **`cyclicPred` at sandwich-T under no-stay ≠ same sandwich-T.** -/
private lemma cyclicPred_ne_self_of_no_stay
    (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (hns : ¬ gc.hasStayAt i)
    (k : Fin gc.configs.length) (hk : gc.moverAt k = i) :
    gc.moverAt (cyclicPred gc.configs_length_pos k) ≠ i := by
  -- Apply cyclicSucc_ne_self_of_no_stay at cyclicPred k:
  -- moverAt(cyclicPred k) = i would make cyclicSucc(cyclicPred k) = k,
  -- so moverAt k = i would equal moverAt at the successor, a stay.
  intro hpred
  have hLpos : 0 < gc.configs.length := gc.configs_length_pos
  have hsucc_eq : cyclicSucc hLpos (cyclicPred hLpos k) = k :=
    cyclicSucc_cyclicPred hLpos k
  have hmover_succ : gc.moverAt (cyclicSucc hLpos (cyclicPred hLpos k)) = i := by
    rw [hsucc_eq]; exact hk
  exact cyclicSucc_ne_self_of_no_stay gc i hns (cyclicPred hLpos k) hpred hmover_succ

/-- **Walker-neighbor locality (pred direction).**

    If `moverAt k = i`, then `moverAt(cyclicPred k) ∈ {left i, i, right i}`.
    Derived from `next_mover_is_local` at `cyclicPred k`, where
    `cyclicSucc(cyclicPred k) = k`. -/
private lemma moverAt_cyclicPred_local
    (gc : GoodCycle sys) (k : Fin gc.configs.length) :
    gc.moverAt (cyclicPred gc.configs_length_pos k) = left (gc.moverAt k) ∨
    gc.moverAt (cyclicPred gc.configs_length_pos k) = gc.moverAt k ∨
    gc.moverAt (cyclicPred gc.configs_length_pos k) = right (gc.moverAt k) := by
  have hLpos : 0 < gc.configs.length := gc.configs_length_pos
  set p := cyclicPred hLpos k with hp_def
  -- We need: nextIndex gc.configs p = k (as a Fin index).
  have hnext_val : (nextIndex gc.configs p).val = k.val := by
    have := cyclicSucc_eq_nextIndex hLpos gc.configs rfl
      ⟨p.val, p.isLt⟩
    -- `this : (cyclicSucc hLpos ⟨p.val, p.isLt⟩).val = (nextIndex gc.configs ⟨p.val, p.isLt⟩).val`
    have hpp : (⟨p.val, p.isLt⟩ : Fin gc.configs.length) = p := Fin.ext rfl
    rw [hpp] at this
    have hsucc_p : cyclicSucc hLpos p = k := by
      rw [hp_def]; exact cyclicSucc_cyclicPred hLpos k
    rw [hsucc_p] at this
    exact this.symm
  have hnext_eq : nextIndex gc.configs p = k := Fin.ext hnext_val
  have hloc := gc.next_mover_is_local p
  simp only at hloc
  rw [hnext_eq] at hloc
  -- hloc : moverAt k = left (moverAt p) ∨ moverAt k = moverAt p ∨ moverAt k = right (moverAt p)
  -- We want: moverAt p ∈ {left (moverAt k), moverAt k, right (moverAt k)}
  -- Solve: from moverAt k = left (moverAt p), get moverAt p = right (moverAt k).
  rcases hloc with hLeft | hSelf | hRight
  · -- moverAt k = left (moverAt p); so moverAt p = right (moverAt k)
    right; right
    have h1 : right (gc.moverAt k) = right (left (gc.moverAt p)) := by rw [hLeft]
    have h2 : right (left (gc.moverAt p)) = gc.moverAt p := right_left_eq_self _
    rw [h1, h2]
  · right; left
    exact hSelf.symm
  · -- moverAt k = right (moverAt p); so moverAt p = left (moverAt k)
    left
    have h1 : left (gc.moverAt k) = left (right (gc.moverAt p)) := by rw [hRight]
    have h2 : left (right (gc.moverAt p)) = gc.moverAt p := left_right_eq_self _
    rw [h1, h2]

/-- `left ⟨1, _⟩ = ⟨0, _⟩` when `n ≥ 2`. -/
private lemma left_one_eq (n : Nat) (hn : 2 ≤ n) :
    (left (⟨1, by omega⟩ : Fin n)) = ⟨0, by omega⟩ := by
  apply Fin.ext
  show (1 + n - 1) % n = 0
  have : 1 + n - 1 = n := by omega
  rw [this, Nat.mod_self]

/-- `right ⟨1, _⟩ = ⟨2, _⟩` when `n ≥ 3`. -/
private lemma right_one_eq (n : Nat) (hn : 3 ≤ n) :
    (right (⟨1, by omega⟩ : Fin n)) = ⟨2, by omega⟩ := by
  apply Fin.ext
  show (1 + 1) % n = 2
  exact Nat.mod_eq_of_lt (by omega)

/-- `left ⟨3, _⟩ = ⟨2, _⟩` when `n ≥ 4`. -/
private lemma left_three_eq (n : Nat) (hn : 4 ≤ n) :
    (left (⟨3, by omega⟩ : Fin n)) = ⟨2, by omega⟩ := by
  apply Fin.ext
  show (3 + n - 1) % n = 2
  have h1 : 3 + n - 1 = n + 2 := by omega
  rw [h1, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- `right ⟨3, _⟩ = ⟨4, _⟩` when `n ≥ 5`. -/
private lemma right_three_eq (n : Nat) (hn : 5 ≤ n) :
    (right (⟨3, by omega⟩ : Fin n)) = ⟨4, by omega⟩ := by
  apply Fin.ext
  show (3 + 1) % n = 4
  exact Nat.mod_eq_of_lt (by omega)

/-- **Image lemma: `cyclicSucc` maps sandwich-T fires to binary fires** under
    both-no-stay. -/
private lemma cyclicSucc_maps_sandwichT_to_binary
    (gc : GoodCycle sys) (hpivot : isPivotFamily sys.rs)
    (hns1 : ¬ gc.hasStayAt ⟨1, by have := hpivot.1; omega⟩)
    (hns3 : ¬ gc.hasStayAt ⟨3, by have := hpivot.1; omega⟩)
    (k : Fin gc.configs.length)
    (hk : k ∈ pivotSandwichTFirePositions gc hpivot) :
    cyclicSucc gc.configs_length_pos k ∈ pivotBinaryFirePositions gc hpivot := by
  have hn := hpivot.1
  unfold pivotSandwichTFirePositions at hk
  unfold pivotBinaryFirePositions
  rw [Finset.mem_filter] at hk ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  obtain ⟨_, hm⟩ := hk
  have hloc := gc.next_mover_is_local k
  simp only at hloc
  have hnext_val : (cyclicSucc gc.configs_length_pos k).val
                   = (nextIndex gc.configs k).val :=
    cyclicSucc_eq_nextIndex gc.configs_length_pos gc.configs rfl k
  have hnext_eq : cyclicSucc gc.configs_length_pos k = nextIndex gc.configs k :=
    Fin.ext hnext_val
  rcases hm with h1 | h3
  · have hne := cyclicSucc_ne_self_of_no_stay gc _ hns1 k h1
    rw [hnext_eq] at hne ⊢
    rw [h1] at hloc
    rcases hloc with hL | hS | hR
    · left; rw [hL]; exact left_one_eq sys.rs.n (by omega)
    · exact absurd hS hne
    · right; left; rw [hR]; exact right_one_eq sys.rs.n (by omega)
  · have hne := cyclicSucc_ne_self_of_no_stay gc _ hns3 k h3
    rw [hnext_eq] at hne ⊢
    rw [h3] at hloc
    rcases hloc with hL | hS | hR
    · right; left; rw [hL]; exact left_three_eq sys.rs.n (by omega)
    · exact absurd hS hne
    · right; right; rw [hR]; exact right_three_eq sys.rs.n (by omega)

/-- **Image lemma: `cyclicPred` maps sandwich-T fires to binary fires** under
    both-no-stay. -/
private lemma cyclicPred_maps_sandwichT_to_binary
    (gc : GoodCycle sys) (hpivot : isPivotFamily sys.rs)
    (hns1 : ¬ gc.hasStayAt ⟨1, by have := hpivot.1; omega⟩)
    (hns3 : ¬ gc.hasStayAt ⟨3, by have := hpivot.1; omega⟩)
    (k : Fin gc.configs.length)
    (hk : k ∈ pivotSandwichTFirePositions gc hpivot) :
    cyclicPred gc.configs_length_pos k ∈ pivotBinaryFirePositions gc hpivot := by
  have hn := hpivot.1
  unfold pivotSandwichTFirePositions at hk
  unfold pivotBinaryFirePositions
  rw [Finset.mem_filter] at hk ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  obtain ⟨_, hm⟩ := hk
  have hloc := moverAt_cyclicPred_local gc k
  rcases hm with h1 | h3
  · have hne := cyclicPred_ne_self_of_no_stay gc _ hns1 k h1
    rw [h1] at hloc
    rcases hloc with hL | hS | hR
    · left; rw [hL]; exact left_one_eq sys.rs.n (by omega)
    · exact absurd hS hne
    · right; left; rw [hR]; exact right_one_eq sys.rs.n (by omega)
  · have hne := cyclicPred_ne_self_of_no_stay gc _ hns3 k h3
    rw [h3] at hloc
    rcases hloc with hL | hS | hR
    · right; left; rw [hL]; exact left_three_eq sys.rs.n (by omega)
    · exact absurd hS hne
    · right; right; rw [hR]; exact right_three_eq sys.rs.n (by omega)

/-- **Step 3 (saturation) — for every binary fire, both walker-neighbors
    are at sandwich-T fires.**

    This is the key combinatorial step of Result 1. Under the no-stay
    hypothesis at both sandwich-Ts, both `cyclicSucc` and `cyclicPred`
    restrict to bijections between sandwich-T fire positions (card 6
    = fc[1] + fc[3] = 3 + 3) and binary fire positions (card 6 =
    fc[0] + fc[2] + fc[4] = 2 + 2 + 2). Surjectivity gives: for every
    `q ∈ pivotBinaryFirePositions`, `cyclicPred q` and `cyclicSucc q`
    both lie in `pivotSandwichTFirePositions`.

    Used to dispatch Steps 4 and 5 via `next_mover_after_proc0_in_1_3`
    and `next_mover_after_proc4_in_1_3`. -/
private theorem result1_step3_saturation
    (gc : GoodCycle sys) (hpivot : isPivotFamily sys.rs)
    (hfc1 : gc.fireCount ⟨1, by have := hpivot.1; omega⟩ = 3)
    (hfc3 : gc.fireCount ⟨3, by have := hpivot.1; omega⟩ = 3)
    (hfc0 : gc.fireCount ⟨0, by have := hpivot.1; omega⟩ = 2)
    (hfc2 : gc.fireCount ⟨2, by have := hpivot.1; omega⟩ = 2)
    (hfc4 : gc.fireCount ⟨4, by have := hpivot.1; omega⟩ = 2)
    (hns1 : ¬ gc.hasStayAt ⟨1, by have := hpivot.1; omega⟩)
    (hns3 : ¬ gc.hasStayAt ⟨3, by have := hpivot.1; omega⟩)
    (q : Fin gc.configs.length)
    (hq : q ∈ pivotBinaryFirePositions gc hpivot) :
    cyclicPred gc.configs_length_pos q ∈ pivotSandwichTFirePositions gc hpivot ∧
    cyclicSucc gc.configs_length_pos q ∈ pivotSandwichTFirePositions gc hpivot := by
  have hLpos : 0 < gc.configs.length := gc.configs_length_pos
  set S := pivotSandwichTFirePositions gc hpivot with hS_def
  set B := pivotBinaryFirePositions gc hpivot with hB_def
  have hS_card : S.card = 6 :=
    pivotSandwichTFirePositions_card gc hpivot hfc1 hfc3
  have hB_card : B.card = 6 :=
    pivotBinaryFirePositions_card gc hpivot hfc0 hfc2 hfc4
  -- σ := cyclicSucc maps S into B, is injective; card-equality → σ(S) = B.
  have h_succ_sub : S.image (cyclicSucc hLpos) ⊆ B := by
    intro q' hq'
    rw [Finset.mem_image] at hq'
    obtain ⟨k, hkS, hkq'⟩ := hq'
    rw [← hkq']
    exact cyclicSucc_maps_sandwichT_to_binary gc hpivot hns1 hns3 k hkS
  have h_succ_card : (S.image (cyclicSucc hLpos)).card = 6 := by
    rw [Finset.card_image_of_injOn
      (fun a _ b _ hab => cyclicSucc_injective hLpos hab)]
    exact hS_card
  have h_succ_eq : S.image (cyclicSucc hLpos) = B :=
    Finset.eq_of_subset_of_card_le h_succ_sub (by rw [h_succ_card, hB_card])
  -- τ := cyclicPred maps S into B, is injective; card-equality → τ(S) = B.
  have h_pred_sub : S.image (cyclicPred hLpos) ⊆ B := by
    intro q' hq'
    rw [Finset.mem_image] at hq'
    obtain ⟨k, hkS, hkq'⟩ := hq'
    rw [← hkq']
    exact cyclicPred_maps_sandwichT_to_binary gc hpivot hns1 hns3 k hkS
  have h_pred_card : (S.image (cyclicPred hLpos)).card = 6 := by
    rw [Finset.card_image_of_injOn
      (fun a _ b _ hab => cyclicPred_injective hLpos hab)]
    exact hS_card
  have h_pred_eq : S.image (cyclicPred hLpos) = B :=
    Finset.eq_of_subset_of_card_le h_pred_sub (by rw [h_pred_card, hB_card])
  refine ⟨?_, ?_⟩
  · -- cyclicPred q ∈ S: use σ(S) = B, so q = σ(k) for some k ∈ S; k = τ(q).
    rw [← h_succ_eq] at hq
    rw [Finset.mem_image] at hq
    obtain ⟨k, hkS, hkq⟩ := hq
    have : cyclicPred hLpos q = k := by
      rw [← hkq]; exact cyclicPred_cyclicSucc hLpos k
    rw [this]; exact hkS
  · -- cyclicSucc q ∈ S: use τ(S) = B.
    rw [← h_pred_eq] at hq
    rw [Finset.mem_image] at hq
    obtain ⟨k, hkS, hkq⟩ := hq
    have : cyclicSucc hLpos q = k := by
      rw [← hkq]; exact cyclicSucc_cyclicPred hLpos k
    rw [this]; exact hkS

/-- **Step 4 (proc 0 forces [1, 0, 1]).**

    Under the Result 1 hypotheses, every proc-0 fire has both its
    walker-neighbors (cyclicPred and cyclicSucc) at proc 1.

    Uses Step 3 saturation + walker-locality intersection `{n-1, 0, 1} ∩ {1, 3} = {1}`. -/
private theorem result1_step4_proc0_cluster
    (gc : GoodCycle sys) (hpivot : isPivotFamily sys.rs)
    (hfc1 : gc.fireCount ⟨1, by have := hpivot.1; omega⟩ = 3)
    (hfc3 : gc.fireCount ⟨3, by have := hpivot.1; omega⟩ = 3)
    (hfc0 : gc.fireCount ⟨0, by have := hpivot.1; omega⟩ = 2)
    (hfc2 : gc.fireCount ⟨2, by have := hpivot.1; omega⟩ = 2)
    (hfc4 : gc.fireCount ⟨4, by have := hpivot.1; omega⟩ = 2)
    (hns1 : ¬ gc.hasStayAt ⟨1, by have := hpivot.1; omega⟩)
    (hns3 : ¬ gc.hasStayAt ⟨3, by have := hpivot.1; omega⟩)
    (q : Fin gc.configs.length)
    (h0 : gc.moverAt q = ⟨0, by have := hpivot.1; omega⟩) :
    gc.moverAt (cyclicPred gc.configs_length_pos q) = ⟨1, by have := hpivot.1; omega⟩ ∧
    gc.moverAt (cyclicSucc gc.configs_length_pos q) = ⟨1, by have := hpivot.1; omega⟩ := by
  have hn := hpivot.1
  have hq_B : q ∈ pivotBinaryFirePositions gc hpivot := by
    unfold pivotBinaryFirePositions
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Or.inl h0⟩
  obtain ⟨hpred_S, hsucc_S⟩ :=
    result1_step3_saturation gc hpivot hfc1 hfc3 hfc0 hfc2 hfc4 hns1 hns3 q hq_B
  unfold pivotSandwichTFirePositions at hpred_S hsucc_S
  rw [Finset.mem_filter] at hpred_S hsucc_S
  have h0val : ((⟨0, by omega⟩ : Fin sys.rs.n)).val = 0 := rfl
  have h3val : ((⟨3, by omega⟩ : Fin sys.rs.n)).val = 3 := rfl
  refine ⟨?_, ?_⟩
  · have hloc := moverAt_cyclicPred_local gc q
    rw [h0] at hloc
    obtain ⟨_, hm⟩ := hpred_S
    rcases hm with h1' | h3'
    · exact h1'
    · exfalso
      rcases hloc with hL | hS | hR
      · have hv : (3 : Nat) = (left (⟨0, by omega⟩ : Fin sys.rs.n)).val := by
          rw [← h3val]; exact congrArg Fin.val (h3'.symm.trans hL)
        rw [left_zero_eq sys.rs.n (by omega)] at hv; omega
      · have hv : (3 : Nat) = 0 := by
          rw [← h3val, ← h0val]
          exact congrArg Fin.val (h3'.symm.trans hS)
        omega
      · have hv : (3 : Nat) = (right (⟨0, by omega⟩ : Fin sys.rs.n)).val := by
          rw [← h3val]; exact congrArg Fin.val (h3'.symm.trans hR)
        rw [right_zero_eq sys.rs.n (by omega)] at hv; omega
  · have hloc := gc.next_mover_is_local q
    simp only at hloc
    have hnext_val : (cyclicSucc gc.configs_length_pos q).val
                     = (nextIndex gc.configs q).val :=
      cyclicSucc_eq_nextIndex gc.configs_length_pos gc.configs rfl q
    have hnext_eq : cyclicSucc gc.configs_length_pos q = nextIndex gc.configs q :=
      Fin.ext hnext_val
    rw [hnext_eq]
    rw [h0] at hloc
    obtain ⟨_, hm⟩ := hsucc_S
    rw [hnext_eq] at hm
    rcases hm with h1' | h3'
    · exact h1'
    · exfalso
      rcases hloc with hL | hS | hR
      · have hv : (3 : Nat) = (left (⟨0, by omega⟩ : Fin sys.rs.n)).val := by
          rw [← h3val]; exact congrArg Fin.val (h3'.symm.trans hL)
        rw [left_zero_eq sys.rs.n (by omega)] at hv; omega
      · have hv : (3 : Nat) = 0 := by
          rw [← h3val, ← h0val]
          exact congrArg Fin.val (h3'.symm.trans hS)
        omega
      · have hv : (3 : Nat) = (right (⟨0, by omega⟩ : Fin sys.rs.n)).val := by
          rw [← h3val]; exact congrArg Fin.val (h3'.symm.trans hR)
        rw [right_zero_eq sys.rs.n (by omega)] at hv; omega

/-- **Step 5 (proc 4 forces [3, 4, 3]).**

    Symmetric to Step 4. Every proc-4 fire has both walker-neighbors
    at proc 3, via intersection `{3, 4, 5} ∩ {1, 3} = {3}`. -/
private theorem result1_step5_proc4_cluster
    (gc : GoodCycle sys) (hpivot : isPivotFamily sys.rs)
    (hfc1 : gc.fireCount ⟨1, by have := hpivot.1; omega⟩ = 3)
    (hfc3 : gc.fireCount ⟨3, by have := hpivot.1; omega⟩ = 3)
    (hfc0 : gc.fireCount ⟨0, by have := hpivot.1; omega⟩ = 2)
    (hfc2 : gc.fireCount ⟨2, by have := hpivot.1; omega⟩ = 2)
    (hfc4 : gc.fireCount ⟨4, by have := hpivot.1; omega⟩ = 2)
    (hns1 : ¬ gc.hasStayAt ⟨1, by have := hpivot.1; omega⟩)
    (hns3 : ¬ gc.hasStayAt ⟨3, by have := hpivot.1; omega⟩)
    (q : Fin gc.configs.length)
    (h4 : gc.moverAt q = ⟨4, by have := hpivot.1; omega⟩) :
    gc.moverAt (cyclicPred gc.configs_length_pos q) = ⟨3, by have := hpivot.1; omega⟩ ∧
    gc.moverAt (cyclicSucc gc.configs_length_pos q) = ⟨3, by have := hpivot.1; omega⟩ := by
  have hn := hpivot.1
  have hq_B : q ∈ pivotBinaryFirePositions gc hpivot := by
    unfold pivotBinaryFirePositions
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Or.inr (Or.inr h4)⟩
  obtain ⟨hpred_S, hsucc_S⟩ :=
    result1_step3_saturation gc hpivot hfc1 hfc3 hfc0 hfc2 hfc4 hns1 hns3 q hq_B
  unfold pivotSandwichTFirePositions at hpred_S hsucc_S
  rw [Finset.mem_filter] at hpred_S hsucc_S
  have h1val : ((⟨1, by omega⟩ : Fin sys.rs.n)).val = 1 := rfl
  have h4val : ((⟨4, by omega⟩ : Fin sys.rs.n)).val = 4 := rfl
  refine ⟨?_, ?_⟩
  · have hloc := moverAt_cyclicPred_local gc q
    rw [h4] at hloc
    obtain ⟨_, hm⟩ := hpred_S
    rcases hm with h1' | h3'
    · exfalso
      rcases hloc with hL | hS | hR
      · have hv : (1 : Nat) = (left (⟨4, by omega⟩ : Fin sys.rs.n)).val := by
          rw [← h1val]; exact congrArg Fin.val (h1'.symm.trans hL)
        rw [left_four_eq sys.rs.n (by omega)] at hv; omega
      · have hv : (1 : Nat) = 4 := by
          rw [← h1val, ← h4val]
          exact congrArg Fin.val (h1'.symm.trans hS)
        omega
      · have hv : (1 : Nat) = (right (⟨4, by omega⟩ : Fin sys.rs.n)).val := by
          rw [← h1val]; exact congrArg Fin.val (h1'.symm.trans hR)
        rw [right_four_eq sys.rs.n (by omega)] at hv; omega
    · exact h3'
  · have hloc := gc.next_mover_is_local q
    simp only at hloc
    have hnext_val : (cyclicSucc gc.configs_length_pos q).val
                     = (nextIndex gc.configs q).val :=
      cyclicSucc_eq_nextIndex gc.configs_length_pos gc.configs rfl q
    have hnext_eq : cyclicSucc gc.configs_length_pos q = nextIndex gc.configs q :=
      Fin.ext hnext_val
    rw [hnext_eq]
    rw [h4] at hloc
    obtain ⟨_, hm⟩ := hsucc_S
    rw [hnext_eq] at hm
    rcases hm with h1' | h3'
    · exfalso
      rcases hloc with hL | hS | hR
      · have hv : (1 : Nat) = (left (⟨4, by omega⟩ : Fin sys.rs.n)).val := by
          rw [← h1val]; exact congrArg Fin.val (h1'.symm.trans hL)
        rw [left_four_eq sys.rs.n (by omega)] at hv; omega
      · have hv : (1 : Nat) = 4 := by
          rw [← h1val, ← h4val]
          exact congrArg Fin.val (h1'.symm.trans hS)
        omega
      · have hv : (1 : Nat) = (right (⟨4, by omega⟩ : Fin sys.rs.n)).val := by
          rw [← h1val]; exact congrArg Fin.val (h1'.symm.trans hR)
        rw [right_four_eq sys.rs.n (by omega)] at hv; omega
    · exact h3'

/-- **Step 6 pigeonhole helper: 4 elements in a 3-element Finset coincide.** -/
private lemma four_elements_in_card3_coincide
    {α : Type*} [DecidableEq α] (S : Finset α) (hS : S.card = 3)
    (a b c d : α) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) :
    a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d := by
  by_contra hall
  push_neg at hall
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := hall
  have h_cd : c ∉ ({d} : Finset α) := by simp [hcd]
  have h_bcd : b ∉ ({c, d} : Finset α) := by simp [hbc, hbd]
  have h_abcd : a ∉ ({b, c, d} : Finset α) := by simp [hab, hac, had]
  have hWcard : ({a, b, c, d} : Finset α).card = 4 := by
    show (insert a (insert b (insert c ({d} : Finset α)))).card = 4
    rw [Finset.card_insert_of_notMem h_abcd,
        Finset.card_insert_of_notMem h_bcd,
        Finset.card_insert_of_notMem h_cd,
        Finset.card_singleton]
  have hWsub : ({a, b, c, d} : Finset α) ⊆ S := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hWsub
  rw [hWcard, hS] at this
  omega

/-- **Step 6 (proc-0 cluster extraction).**

    Under the Result 1 hypotheses, there exist two proc-0 fires `q₁, q₂`
    such that their walker-neighbors form the `[1, 0, 1, 0, 1]` cluster.
    Equivalently: there is a position `p` such that
    `moverAt p = moverAt (p + 2) = 0` and
    `moverAt (p - 1) = moverAt (p + 1) = moverAt (p + 3) = 1`. -/
private theorem result1_step6_proc0_cluster_exists
    (gc : GoodCycle sys) (hpivot : isPivotFamily sys.rs)
    (hfc1 : gc.fireCount ⟨1, by have := hpivot.1; omega⟩ = 3)
    (hfc3 : gc.fireCount ⟨3, by have := hpivot.1; omega⟩ = 3)
    (hfc0 : gc.fireCount ⟨0, by have := hpivot.1; omega⟩ = 2)
    (hfc2 : gc.fireCount ⟨2, by have := hpivot.1; omega⟩ = 2)
    (hfc4 : gc.fireCount ⟨4, by have := hpivot.1; omega⟩ = 2)
    (hns1 : ¬ gc.hasStayAt ⟨1, by have := hpivot.1; omega⟩)
    (hns3 : ¬ gc.hasStayAt ⟨3, by have := hpivot.1; omega⟩) :
    ∃ p : Fin gc.configs.length,
      gc.moverAt p = ⟨0, by have := hpivot.1; omega⟩ ∧
      gc.moverAt (cyclicSucc gc.configs_length_pos
        (cyclicSucc gc.configs_length_pos p))
        = ⟨0, by have := hpivot.1; omega⟩ ∧
      gc.moverAt (cyclicPred gc.configs_length_pos p)
        = ⟨1, by have := hpivot.1; omega⟩ ∧
      gc.moverAt (cyclicSucc gc.configs_length_pos p)
        = ⟨1, by have := hpivot.1; omega⟩ ∧
      gc.moverAt (cyclicSucc gc.configs_length_pos
        (cyclicSucc gc.configs_length_pos (cyclicSucc gc.configs_length_pos p)))
        = ⟨1, by have := hpivot.1; omega⟩ := by
  have hn := hpivot.1
  have hLpos : 0 < gc.configs.length := gc.configs_length_pos
  -- Derive L ≥ 3 from three distinct proc-1 fires.
  have hL_ge3 : gc.configs.length ≥ 3 := by
    have hfc1_ge : gc.fireCount ⟨1, by omega⟩ ≥ 3 := by rw [hfc1]
    obtain ⟨f₀, f₁, f₂, hf01, hf12, _, _, _⟩ :=
      exists_three_firing_steps_of_ge3 gc ⟨1, by omega⟩ hfc1_ge
    have := f₂.isLt
    omega
  -- Extract two proc-0 fires q₁ < q₂.
  have hbin0 : isBinary sys.rs ⟨0, by omega⟩ := by
    unfold isBinary
    exact hpivot.2.1 ⟨0, by omega⟩ (by simp)
  have hfc0_pos : gc.fireCount ⟨0, by omega⟩ > 0 := by rw [hfc0]; omega
  obtain ⟨q₁, q₂, hlt_q, h0_q₁, h0_q₂⟩ :=
    exists_two_firing_steps gc ⟨0, by omega⟩ hbin0 hfc0_pos
  have hne_q : q₁ ≠ q₂ := fun h => Nat.lt_irrefl _ (h ▸ hlt_q)
  -- Apply Step 4 to each proc-0 fire.
  obtain ⟨hpred1, hsucc1⟩ :=
    result1_step4_proc0_cluster gc hpivot hfc1 hfc3 hfc0 hfc2 hfc4 hns1 hns3 q₁ h0_q₁
  obtain ⟨hpred2, hsucc2⟩ :=
    result1_step4_proc0_cluster gc hpivot hfc1 hfc3 hfc0 hfc2 hfc4 hns1 hns3 q₂ h0_q₂
  -- Name the 4 walker-neighbors.
  set a := cyclicPred hLpos q₁
  set b := cyclicSucc hLpos q₁
  set c := cyclicPred hLpos q₂
  set d := cyclicSucc hLpos q₂
  -- All 4 are in the proc-1 fire set (card 3 via fc[1]).
  let proc1Set : Finset (Fin gc.configs.length) :=
    Finset.univ.filter
      (fun k : Fin gc.configs.length => gc.moverAt k = ⟨1, by omega⟩)
  have hproc1_card : proc1Set.card = 3 := by
    show (Finset.univ.filter
      (fun k : Fin gc.configs.length => gc.moverAt k = ⟨1, by omega⟩)).card = 3
    rw [firePositions_card_eq_fireCount]; exact hfc1
  have ha_mem : a ∈ proc1Set := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpred1⟩
  have hb_mem : b ∈ proc1Set := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsucc1⟩
  have hc_mem : c ∈ proc1Set := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpred2⟩
  have hd_mem : d ∈ proc1Set := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsucc2⟩
  -- Pigeonhole: some pair of {a, b, c, d} coincides.
  have h_coincide :=
    four_elements_in_card3_coincide proc1Set hproc1_card a b c d
      ha_mem hb_mem hc_mem hd_mem
  -- Eliminate impossible cases, derive cluster from valid ones.
  -- Impossible: a=b, c=d (would need L | 2, but L ≥ 3),
  --             a=c, b=d (would need q₁ = q₂ by inj, contradiction).
  -- Valid: a=d → cluster at p := q₂, b=c → cluster at p := q₁.
  have hL_not_dvd_2 : ¬ gc.configs.length ∣ 2 := by
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  rcases h_coincide with hab | hac | had | hbc | hbd | hcd
  · -- a = b impossible: cyclicPred q₁ = cyclicSucc q₁ ⇒ q₁ = cyclicSucc² q₁.
    exfalso
    have hstep : cyclicSucc hLpos a = cyclicSucc hLpos b := congrArg _ hab
    have hstep1 : cyclicSucc hLpos a = q₁ := cyclicSucc_cyclicPred hLpos q₁
    have hstep2 :
        cyclicSucc hLpos b = cyclicSucc hLpos (cyclicSucc hLpos q₁) := rfl
    have hfinal : q₁ = cyclicSucc hLpos (cyclicSucc hLpos q₁) :=
      hstep1.symm.trans (hstep.trans hstep2)
    have hval : q₁.val = ((q₁.val + 1) % gc.configs.length + 1) % gc.configs.length := by
      have := congrArg Fin.val hfinal
      simpa [cyclicSucc] using this
    apply hL_not_dvd_2
    have hqlt := q₁.isLt
    by_cases h1 : q₁.val + 1 < gc.configs.length
    · rw [Nat.mod_eq_of_lt h1] at hval
      by_cases h2 : q₁.val + 1 + 1 < gc.configs.length
      · rw [Nat.mod_eq_of_lt h2] at hval; omega
      · push_neg at h2
        have h2eq : q₁.val + 1 + 1 = gc.configs.length := by omega
        rw [h2eq, Nat.mod_self] at hval
        omega
    · push_neg at h1
      have h1eq : q₁.val + 1 = gc.configs.length := by omega
      rw [h1eq, Nat.mod_self] at hval
      have : ((0 : Nat) + 1) % gc.configs.length = 1 := by
        rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
      rw [this] at hval
      omega
  · -- a = c impossible: cyclicPred q₁ = cyclicPred q₂ → q₁ = q₂ by inj.
    exfalso
    exact hne_q (cyclicPred_injective hLpos hac)
  · -- a = d valid: cyclicPred q₁ = cyclicSucc q₂. Cluster at p := q₂.
    refine ⟨q₂, h0_q₂, ?_, ?_, ?_, ?_⟩
    · -- cyclicSucc²(q₂) = cyclicSucc(d) = cyclicSucc(cyclicPred q₁) = q₁, moverAt = 0.
      have : cyclicSucc hLpos (cyclicSucc hLpos q₂) = q₁ := by
        show cyclicSucc hLpos d = q₁
        rw [← had]
        exact cyclicSucc_cyclicPred hLpos q₁
      rw [this]; exact h0_q₁
    · -- cyclicPred q₂ = c, moverAt = 1.
      show gc.moverAt c = _; exact hpred2
    · -- cyclicSucc q₂ = d, moverAt = 1.
      show gc.moverAt d = _; exact hsucc2
    · -- cyclicSucc³(q₂) = cyclicSucc(q₁) = b, moverAt = 1.
      have h_s2q2 : cyclicSucc hLpos (cyclicSucc hLpos q₂) = q₁ := by
        show cyclicSucc hLpos d = q₁
        rw [← had]
        exact cyclicSucc_cyclicPred hLpos q₁
      rw [h_s2q2]; exact hsucc1
  · -- b = c valid: cyclicSucc q₁ = cyclicPred q₂. Cluster at p := q₁.
    refine ⟨q₁, h0_q₁, ?_, ?_, ?_, ?_⟩
    · -- cyclicSucc²(q₁) = cyclicSucc(b) = cyclicSucc(cyclicPred q₂) = q₂, moverAt = 0.
      have : cyclicSucc hLpos (cyclicSucc hLpos q₁) = q₂ := by
        show cyclicSucc hLpos b = q₂
        rw [hbc]
        exact cyclicSucc_cyclicPred hLpos q₂
      rw [this]; exact h0_q₂
    · -- cyclicPred q₁ = a, moverAt = 1.
      show gc.moverAt a = _; exact hpred1
    · -- cyclicSucc q₁ = b, moverAt = 1.
      show gc.moverAt b = _; exact hsucc1
    · -- cyclicSucc³(q₁) = cyclicSucc(q₂) = d, moverAt = 1.
      have h_s2q1 : cyclicSucc hLpos (cyclicSucc hLpos q₁) = q₂ := by
        show cyclicSucc hLpos b = q₂
        rw [hbc]
        exact cyclicSucc_cyclicPred hLpos q₂
      rw [h_s2q1]; exact hsucc2
  · -- b = d impossible: cyclicSucc q₁ = cyclicSucc q₂ → q₁ = q₂ by inj.
    exfalso
    exact hne_q (cyclicSucc_injective hLpos hbd)
  · -- c = d impossible: same as a = b case with q₂.
    exfalso
    have hstep : cyclicSucc hLpos c = cyclicSucc hLpos d := congrArg _ hcd
    have hstep1 : cyclicSucc hLpos c = q₂ := cyclicSucc_cyclicPred hLpos q₂
    have hstep2 :
        cyclicSucc hLpos d = cyclicSucc hLpos (cyclicSucc hLpos q₂) := rfl
    have hfinal : q₂ = cyclicSucc hLpos (cyclicSucc hLpos q₂) :=
      hstep1.symm.trans (hstep.trans hstep2)
    have hval : q₂.val = ((q₂.val + 1) % gc.configs.length + 1) % gc.configs.length := by
      have := congrArg Fin.val hfinal
      simpa [cyclicSucc] using this
    apply hL_not_dvd_2
    have hqlt := q₂.isLt
    by_cases h1 : q₂.val + 1 < gc.configs.length
    · rw [Nat.mod_eq_of_lt h1] at hval
      by_cases h2 : q₂.val + 1 + 1 < gc.configs.length
      · rw [Nat.mod_eq_of_lt h2] at hval; omega
      · push_neg at h2
        have h2eq : q₂.val + 1 + 1 = gc.configs.length := by omega
        rw [h2eq, Nat.mod_self] at hval
        omega
    · push_neg at h1
      have h1eq : q₂.val + 1 = gc.configs.length := by omega
      rw [h1eq, Nat.mod_self] at hval
      have : ((0 : Nat) + 1) % gc.configs.length = 1 := by
        rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
      rw [this] at hval
      omega

/-- **Step 7 (proc-4 cluster extraction).**

    Symmetric to Step 6: exists `p'` with proc-4 fires at `{p', p' + 2}`
    and proc-3 fires at `{p' - 1, p' + 1, p' + 3}`. -/
private theorem result1_step7_proc4_cluster_exists
    (gc : GoodCycle sys) (hpivot : isPivotFamily sys.rs)
    (hfc1 : gc.fireCount ⟨1, by have := hpivot.1; omega⟩ = 3)
    (hfc3 : gc.fireCount ⟨3, by have := hpivot.1; omega⟩ = 3)
    (hfc0 : gc.fireCount ⟨0, by have := hpivot.1; omega⟩ = 2)
    (hfc2 : gc.fireCount ⟨2, by have := hpivot.1; omega⟩ = 2)
    (hfc4 : gc.fireCount ⟨4, by have := hpivot.1; omega⟩ = 2)
    (hns1 : ¬ gc.hasStayAt ⟨1, by have := hpivot.1; omega⟩)
    (hns3 : ¬ gc.hasStayAt ⟨3, by have := hpivot.1; omega⟩) :
    ∃ p : Fin gc.configs.length,
      gc.moverAt p = ⟨4, by have := hpivot.1; omega⟩ ∧
      gc.moverAt (cyclicSucc gc.configs_length_pos
        (cyclicSucc gc.configs_length_pos p))
        = ⟨4, by have := hpivot.1; omega⟩ ∧
      gc.moverAt (cyclicPred gc.configs_length_pos p)
        = ⟨3, by have := hpivot.1; omega⟩ ∧
      gc.moverAt (cyclicSucc gc.configs_length_pos p)
        = ⟨3, by have := hpivot.1; omega⟩ ∧
      gc.moverAt (cyclicSucc gc.configs_length_pos
        (cyclicSucc gc.configs_length_pos (cyclicSucc gc.configs_length_pos p)))
        = ⟨3, by have := hpivot.1; omega⟩ := by
  have hn := hpivot.1
  have hLpos : 0 < gc.configs.length := gc.configs_length_pos
  have hL_ge3 : gc.configs.length ≥ 3 := by
    have hfc3_ge : gc.fireCount ⟨3, by omega⟩ ≥ 3 := by rw [hfc3]
    obtain ⟨_, _, f₂, _, _, _, _, _⟩ :=
      exists_three_firing_steps_of_ge3 gc ⟨3, by omega⟩ hfc3_ge
    have := f₂.isLt
    omega
  have hbin4 : isBinary sys.rs ⟨4, by omega⟩ := by
    unfold isBinary
    exact hpivot.2.1 ⟨4, by omega⟩ (by simp)
  have hfc4_pos : gc.fireCount ⟨4, by omega⟩ > 0 := by rw [hfc4]; omega
  obtain ⟨q₁, q₂, hlt_q, h4_q₁, h4_q₂⟩ :=
    exists_two_firing_steps gc ⟨4, by omega⟩ hbin4 hfc4_pos
  have hne_q : q₁ ≠ q₂ := fun h => Nat.lt_irrefl _ (h ▸ hlt_q)
  obtain ⟨hpred1, hsucc1⟩ :=
    result1_step5_proc4_cluster gc hpivot hfc1 hfc3 hfc0 hfc2 hfc4 hns1 hns3 q₁ h4_q₁
  obtain ⟨hpred2, hsucc2⟩ :=
    result1_step5_proc4_cluster gc hpivot hfc1 hfc3 hfc0 hfc2 hfc4 hns1 hns3 q₂ h4_q₂
  set a := cyclicPred hLpos q₁
  set b := cyclicSucc hLpos q₁
  set c := cyclicPred hLpos q₂
  set d := cyclicSucc hLpos q₂
  let proc3Set : Finset (Fin gc.configs.length) :=
    Finset.univ.filter
      (fun k : Fin gc.configs.length => gc.moverAt k = ⟨3, by omega⟩)
  have hproc3_card : proc3Set.card = 3 := by
    show (Finset.univ.filter
      (fun k : Fin gc.configs.length => gc.moverAt k = ⟨3, by omega⟩)).card = 3
    rw [firePositions_card_eq_fireCount]; exact hfc3
  have ha_mem : a ∈ proc3Set := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpred1⟩
  have hb_mem : b ∈ proc3Set := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsucc1⟩
  have hc_mem : c ∈ proc3Set := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpred2⟩
  have hd_mem : d ∈ proc3Set := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsucc2⟩
  have h_coincide :=
    four_elements_in_card3_coincide proc3Set hproc3_card a b c d
      ha_mem hb_mem hc_mem hd_mem
  have hL_not_dvd_2 : ¬ gc.configs.length ∣ 2 := by
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  rcases h_coincide with hab | hac | had | hbc | hbd | hcd
  · exfalso
    have hstep : cyclicSucc hLpos a = cyclicSucc hLpos b := congrArg _ hab
    have hstep1 : cyclicSucc hLpos a = q₁ := cyclicSucc_cyclicPred hLpos q₁
    have hstep2 :
        cyclicSucc hLpos b = cyclicSucc hLpos (cyclicSucc hLpos q₁) := rfl
    have hfinal : q₁ = cyclicSucc hLpos (cyclicSucc hLpos q₁) :=
      hstep1.symm.trans (hstep.trans hstep2)
    have hval : q₁.val = ((q₁.val + 1) % gc.configs.length + 1) % gc.configs.length := by
      have := congrArg Fin.val hfinal
      simpa [cyclicSucc] using this
    apply hL_not_dvd_2
    have hqlt := q₁.isLt
    by_cases h1 : q₁.val + 1 < gc.configs.length
    · rw [Nat.mod_eq_of_lt h1] at hval
      by_cases h2 : q₁.val + 1 + 1 < gc.configs.length
      · rw [Nat.mod_eq_of_lt h2] at hval; omega
      · push_neg at h2
        have h2eq : q₁.val + 1 + 1 = gc.configs.length := by omega
        rw [h2eq, Nat.mod_self] at hval
        omega
    · push_neg at h1
      have h1eq : q₁.val + 1 = gc.configs.length := by omega
      rw [h1eq, Nat.mod_self] at hval
      have : ((0 : Nat) + 1) % gc.configs.length = 1 := by
        rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
      rw [this] at hval
      omega
  · exfalso
    exact hne_q (cyclicPred_injective hLpos hac)
  · refine ⟨q₂, h4_q₂, ?_, ?_, ?_, ?_⟩
    · have : cyclicSucc hLpos (cyclicSucc hLpos q₂) = q₁ := by
        show cyclicSucc hLpos d = q₁
        rw [← had]
        exact cyclicSucc_cyclicPred hLpos q₁
      rw [this]; exact h4_q₁
    · show gc.moverAt c = _; exact hpred2
    · show gc.moverAt d = _; exact hsucc2
    · have h_s2q2 : cyclicSucc hLpos (cyclicSucc hLpos q₂) = q₁ := by
        show cyclicSucc hLpos d = q₁
        rw [← had]
        exact cyclicSucc_cyclicPred hLpos q₁
      rw [h_s2q2]; exact hsucc1
  · refine ⟨q₁, h4_q₁, ?_, ?_, ?_, ?_⟩
    · have : cyclicSucc hLpos (cyclicSucc hLpos q₁) = q₂ := by
        show cyclicSucc hLpos b = q₂
        rw [hbc]
        exact cyclicSucc_cyclicPred hLpos q₂
      rw [this]; exact h4_q₂
    · show gc.moverAt a = _; exact hpred1
    · show gc.moverAt b = _; exact hsucc1
    · have h_s2q1 : cyclicSucc hLpos (cyclicSucc hLpos q₁) = q₂ := by
        show cyclicSucc hLpos b = q₂
        rw [hbc]
        exact cyclicSucc_cyclicPred hLpos q₂
      rw [h_s2q1]; exact hsucc2
  · exfalso
    exact hne_q (cyclicSucc_injective hLpos hbd)
  · exfalso
    have hstep : cyclicSucc hLpos c = cyclicSucc hLpos d := congrArg _ hcd
    have hstep1 : cyclicSucc hLpos c = q₂ := cyclicSucc_cyclicPred hLpos q₂
    have hstep2 :
        cyclicSucc hLpos d = cyclicSucc hLpos (cyclicSucc hLpos q₂) := rfl
    have hfinal : q₂ = cyclicSucc hLpos (cyclicSucc hLpos q₂) :=
      hstep1.symm.trans (hstep.trans hstep2)
    have hval : q₂.val = ((q₂.val + 1) % gc.configs.length + 1) % gc.configs.length := by
      have := congrArg Fin.val hfinal
      simpa [cyclicSucc] using this
    apply hL_not_dvd_2
    have hqlt := q₂.isLt
    by_cases h1 : q₂.val + 1 < gc.configs.length
    · rw [Nat.mod_eq_of_lt h1] at hval
      by_cases h2 : q₂.val + 1 + 1 < gc.configs.length
      · rw [Nat.mod_eq_of_lt h2] at hval; omega
      · push_neg at h2
        have h2eq : q₂.val + 1 + 1 = gc.configs.length := by omega
        rw [h2eq, Nat.mod_self] at hval
        omega
    · push_neg at h1
      have h1eq : q₂.val + 1 = gc.configs.length := by omega
      rw [h1eq, Nat.mod_self] at hval
      have : ((0 : Nat) + 1) % gc.configs.length = 1 := by
        rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
      rw [this] at hval
      omega

/-- **Result 1 — both sandwich-Ts can't be no-stay.**

    In any Path A pivot min-CL good cycle with sandwich-Ts at positions
    1 and 3, it is NOT the case that both simultaneously lack a
    (cyclic) stay.

    Proof strategy: slot-count saturation ruling out the joint
    no-stay configuration via walker trapping. Full analytical proof
    in `docs/lean_docs/lb_campaign_2026-04-12/linear_stay_lemma_attempt_2026-04-14.md`.

    This lemma is used by the L4d rotation-invariance closure:
    the double-(1,1,0) failure row at both sandwich-Ts implies both
    are "no linear stay", and Case A of the closure (both actually
    no-stay, not wrap-stay) contradicts this theorem directly. -/
theorem result1_both_sandwich_stays
    (gc : GoodCycle sys)
    (hpivot : isPivotFamily sys.rs)
    (hfc1 : gc.fireCount ⟨1, by have := hpivot.1; omega⟩ = 3)
    (hfc3 : gc.fireCount ⟨3, by have := hpivot.1; omega⟩ = 3)
    (hfc0 : gc.fireCount ⟨0, by have := hpivot.1; omega⟩ = 2)
    (hfc2 : gc.fireCount ⟨2, by have := hpivot.1; omega⟩ = 2)
    (hfc4 : gc.fireCount ⟨4, by have := hpivot.1; omega⟩ = 2) :
    ¬ (¬ gc.hasStayAt ⟨1, by have := hpivot.1; omega⟩ ∧
       ¬ gc.hasStayAt ⟨3, by have := hpivot.1; omega⟩) := by
  -- Step 1 (slot count): each sandwich-T has 3 fires × 2 slot instances
  -- (pred + succ) = 6 slot instances per sandwich-T × 2 sandwich-Ts = 12.
  --
  -- Step 2 (binary contribution bound): each of the 6 binary fires
  -- (fc[0] + fc[2] + fc[4] = 2 + 2 + 2 = 6) contributes at most 2
  -- slot instances, max total = 12.
  --
  -- Step 3 (saturation): 12 slot instances demand 12 binary
  -- contributions; equality forces every binary fire to have both
  -- walker-neighbors in {1, 3} (the sandwich-T set).
  --
  -- Step 4 (proc 0 forces [1, 0, 1]): walker-locality at proc 0-fire
  -- gives neighbors in {left 0, 0, right 0} = {n-1, 0, 1}. Intersect
  -- with {1, 3}: singleton {1}. So both neighbors of every proc 0
  -- fire are at proc 1.
  --
  -- Step 5 (proc 4 forces [3, 4, 3]): symmetric to Step 4.
  --
  -- Step 6 (proc 0 cluster [1, 0, 1, 0, 1]): two proc-0 fires at
  -- positions p_01, p_02 with p_02 = p_01 + 2, giving a 5-position
  -- walker sequence [1, 0, 1, 0, 1]. This consumes fc[0] = 2 and
  -- fc[1] = 3 entirely.
  --
  -- Step 7 (proc 4 cluster [3, 4, 3, 4, 3]): symmetric to Step 6.
  --
  -- Step 8 (proc 2 bridging): the 2 proc-2 fires must also satisfy
  -- walker-adjacency: both neighbors in {left 2, 2, right 2} ∩ {1, 3}
  -- = {1, 3}. The only positions where this works are where proc 2
  -- bridges between the two clusters.
  --
  -- Step 9 (walker trap): the assembled near-cluster block
  -- [1, 0, 1, 0, 1, 2, 3, 4, 3, 4, 3, 2] has walker at proc 2 at the
  -- boundary, and next_mover_is_local forces the next position into
  -- {1, 2, 3}, none of which is an outer proc in {5, ..., n-1}.
  -- Walker is trapped, contradicting the need to fire outer procs.
  intro ⟨hno_stay_1, hno_stay_3⟩
  have hn := hpivot.1
  have hLpos : 0 < gc.configs.length := gc.configs_length_pos
  -- Extract a proc-0 fire via Step 6 (we only need existence, not the cluster).
  obtain ⟨p₀, h0p₀, _, _, _, _⟩ :=
    result1_step6_proc0_cluster_exists gc hpivot hfc1 hfc3 hfc0 hfc2 hfc4
      hno_stay_1 hno_stay_3
  -- **Step 8-9 Walker Trap.** Under Steps 3-7, the walker is closed under
  -- `cyclicSucc` in `{0, 1, 2, 3, 4}`: from any position with mover ≤ 4,
  -- the next walker position also has mover ≤ 4. Since `p₀` has mover 0,
  -- iteration of `cyclicSucc` shows every position has mover ≤ 4. But proc
  -- 5 must fire (by `fireCount_pos_of_fair`), giving a contradiction.
  have hwalker_closed_step : ∀ k : Fin gc.configs.length,
      (gc.moverAt k).val ≤ 4 →
      (gc.moverAt (cyclicSucc hLpos k)).val ≤ 4 := by
    intro k hle
    -- Case on (gc.moverAt k).val ∈ {0, 1, 2, 3, 4}.
    -- Binary cases (0, 2, 4): use Step 3 saturation → cyclicSucc k ∈ sandwichT.
    -- Sandwich-T cases (1, 3): use cyclicSucc_maps_sandwichT_to_binary.
    by_cases hB : gc.moverAt k = ⟨0, by omega⟩ ∨ gc.moverAt k = ⟨2, by omega⟩ ∨
                  gc.moverAt k = ⟨4, by omega⟩
    · have hkB : k ∈ pivotBinaryFirePositions gc hpivot := by
        unfold pivotBinaryFirePositions
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hB⟩
      have hsucc_S :=
        (result1_step3_saturation gc hpivot hfc1 hfc3 hfc0 hfc2 hfc4
          hno_stay_1 hno_stay_3 k hkB).2
      unfold pivotSandwichTFirePositions at hsucc_S
      rw [Finset.mem_filter] at hsucc_S
      rcases hsucc_S.2 with h1 | h3
      · have hv : (gc.moverAt (cyclicSucc hLpos k)).val = 1 := by rw [h1]
        omega
      · have hv : (gc.moverAt (cyclicSucc hLpos k)).val = 3 := by rw [h3]
        omega
    · -- Not in binary. So mover ∈ {1, 3} (excluding ≥5 by hle).
      push_neg at hB
      obtain ⟨hne0, hne2, hne4⟩ := hB
      have hval := (gc.moverAt k).isLt
      have hkval_le : (gc.moverAt k).val ≤ 4 := hle
      have hkval_ne0 : (gc.moverAt k).val ≠ 0 := by
        intro h; apply hne0; exact Fin.ext h
      have hkval_ne2 : (gc.moverAt k).val ≠ 2 := by
        intro h; apply hne2; exact Fin.ext h
      have hkval_ne4 : (gc.moverAt k).val ≠ 4 := by
        intro h; apply hne4; exact Fin.ext h
      have hkval_13 : (gc.moverAt k).val = 1 ∨ (gc.moverAt k).val = 3 := by omega
      have hkS : k ∈ pivotSandwichTFirePositions gc hpivot := by
        unfold pivotSandwichTFirePositions
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases hkval_13 with h1 | h3
        · left; exact Fin.ext h1
        · right; exact Fin.ext h3
      have hsucc_B :=
        cyclicSucc_maps_sandwichT_to_binary gc hpivot hno_stay_1 hno_stay_3 k hkS
      unfold pivotBinaryFirePositions at hsucc_B
      rw [Finset.mem_filter] at hsucc_B
      rcases hsucc_B.2 with h0 | h2 | h4
      · have hv : (gc.moverAt (cyclicSucc hLpos k)).val = 0 := by rw [h0]
        omega
      · have hv : (gc.moverAt (cyclicSucc hLpos k)).val = 2 := by rw [h2]
        omega
      · have hv : (gc.moverAt (cyclicSucc hLpos k)).val = 4 := by rw [h4]
        omega
  -- Use orbit coverage: from p₀ we reach every position via iteration.
  have hwalker_trap : ∀ k : Fin gc.configs.length, (gc.moverAt k).val ≤ 4 := by
    intro k
    obtain ⟨m, hm⟩ := cyclicSucc_orbit_univ hLpos p₀ k
    rw [← hm]
    clear hm
    induction m with
    | zero =>
      show (gc.moverAt p₀).val ≤ 4
      rw [h0p₀]; simp
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact hwalker_closed_step _ ih
  -- Contradict with fairness: proc 5 must fire in the good cycle.
  obtain ⟨k₅, j₅, hpriv₅, _, hj₅⟩ := gc.fair ⟨5, by omega⟩
  have hk₅_mover : gc.moverAt k₅ = ⟨5, by omega⟩ := by
    rw [← hj₅]; exact (gc.moverAt_unique k₅ j₅ hpriv₅).symm
  have h5_le_4 : (gc.moverAt k₅).val ≤ 4 := hwalker_trap k₅
  rw [hk₅_mover] at h5_le_4
  have : (5 : Nat) ≤ 4 := h5_le_4
  omega

/-- **Result 1' — one-wrap-stay variant (Case B of L4d).**

    Extends Result 1 to the asymmetric "one sandwich-T has no stay,
    the other has only a wrap stay" configuration. In Path A pivot
    min-CL with `n ≥ 9`, this is impossible.

    Proof: slot-count saturation under the wrap-stay structural
    constraints (`moverAt 0 = moverAt (L-1) = j`), refined case
    analysis on the forced binary fires at positions 1 and `L-2`
    (which must be in {proc 2, proc 4} by locality). Full analytical
    proof in
    `docs/lean_docs/lb_campaign_2026-04-12/result1_prime_asymmetric_2026-04-14.md`.

    **Used in**: `l4d_no_linear_stay_both_sandwich_impossible` Case B
    (`¬hasWrapStayAt 1, hasWrapStayAt 3, ¬hasLinearStayAt 1, ¬hasLinearStayAt 3`).

    **Status**: structural stub; full case analysis pending port. -/
theorem result1_prime_one_wrap_stay
    (gc : GoodCycle sys)
    (hpivot : isPivotFamily sys.rs)
    (hfc1 : gc.fireCount ⟨1, by have := hpivot.1; omega⟩ = 3)
    (hfc3 : gc.fireCount ⟨3, by have := hpivot.1; omega⟩ = 3)
    (hfc0 : gc.fireCount ⟨0, by have := hpivot.1; omega⟩ = 2)
    (hfc2 : gc.fireCount ⟨2, by have := hpivot.1; omega⟩ = 2)
    (hfc4 : gc.fireCount ⟨4, by have := hpivot.1; omega⟩ = 2)
    (hns1 : ¬ gc.hasStayAt ⟨1, by have := hpivot.1; omega⟩)
    (hws3 : gc.hasWrapStayAt ⟨3, by have := hpivot.1; omega⟩)
    (hnls3 : ¬ gc.hasLinearStayAt ⟨3, by have := hpivot.1; omega⟩) :
    False := by
  -- Proof decomposition (see result1_prime_asymmetric doc):
  --
  --   Fact 3.1-3.4: wrap stay at proc 3 ⟹ moverAt(0) = moverAt(L-1) = 3,
  --   third proc-3 fire at k_int ∈ [2, L-3], positions 1 and L-2 are
  --   binary fires at proc 2 or proc 4 (by locality + hnls3).
  --
  --   Slot count: S = 10 walker-neighbor-binary instances from
  --   sandwich-Ts (6 from proc 1, 4 from proc 3 with wrap-stay
  --   discount of 2).
  --
  --   Case split on (moverAt(1), moverAt(L-2)) ∈ {2, 4} × {2, 4}:
  --     B.i.a (2, 2): cluster collision forces |2 - (L-3)| ≤ 4 ⟹ L ≤ 9 < 24.
  --     B.i.b (2, 4): no valid second proc-4 fire.
  --     B.i.c (4, 2): mirror of B.i.b.
  --     B.iii (4, 4): further split on (moverAt(2), moverAt(L-3)) ∈ {3, 5}^2.
  --       B.iii.α/β: one=3, other=5. moverAt(4) ∈ {1, 2} exhausted by
  --         walker-length mismatch (3n - 15 ≠ 2n - 10 for n ≥ 9).
  --       B.iii.γ: both=5. proc-1 cluster AP mismatch with
  --         {L-3, 2, k_int±2}.
  sorry

/-- **Result 1' mirror — Case C of L4d.**

    Symmetric to `result1_prime_one_wrap_stay` under the
    `i ↦ 4 - i` automorphism of the pivot family. -/
theorem result1_prime_one_wrap_stay_mirror
    (gc : GoodCycle sys)
    (hpivot : isPivotFamily sys.rs)
    (hfc1 : gc.fireCount ⟨1, by have := hpivot.1; omega⟩ = 3)
    (hfc3 : gc.fireCount ⟨3, by have := hpivot.1; omega⟩ = 3)
    (hfc0 : gc.fireCount ⟨0, by have := hpivot.1; omega⟩ = 2)
    (hfc2 : gc.fireCount ⟨2, by have := hpivot.1; omega⟩ = 2)
    (hfc4 : gc.fireCount ⟨4, by have := hpivot.1; omega⟩ = 2)
    (hws1 : gc.hasWrapStayAt ⟨1, by have := hpivot.1; omega⟩)
    (hnls1 : ¬ gc.hasLinearStayAt ⟨1, by have := hpivot.1; omega⟩)
    (hns3 : ¬ gc.hasStayAt ⟨3, by have := hpivot.1; omega⟩) :
    False := by
  sorry

end LeanMn
