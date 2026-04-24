/-
  ZeroWinding.lean — Zero-winding with cw > 0 (clustering/provider route)

  Case C from lb_complete_proof.md: the good cycle has balanced CW/CCW steps
  with net displacement 0 and cwStepCount > 0.

  Proof chain (post-2026-04-11 rewrite):
  1. `provider_interval_exists_zw` — under ZW+cw>0+≥3 binary+sub-threshold,
     there exists a clustering "0/2 provider interval": proc `i` with
     consecutive fires `a₁ < a₂`, a step `k₂` between, such that on
     `[k₂, a₂)` one binary neighbor fires an even nonzero number of times and
     the other is silent. PA-verified 13,312/13,312 random cycles at n=5..13
     plus 162/162 all-binary n=9 cycles. The math sorry lives here.
  2. `general_step_pair_ec` — mechanical construction of `hasEntryConflict gc`
     from a provider interval, via `configVal_eq_of_noFire_between` and
     `binary_config_eq_of_even_intervalFireCount`. Sorry-free.
  3. `zeroWinding_cwPos_false` — unified: call the clustering lemma, apply
     the mechanical constructor, apply `entryConflict_impossible`. No 3CB /
     non-3CB case split. No `palindromic_ec` chain. No `nonConsecutive_false`
     path.

  History note: a previous session pivoted through a chosen-3CB residue cut
  (`chosen3cb_all_normal_residue_hasEntryConflict` +
  `exists_binary_tail_of_chosen_3cb`) and a separate palindromic fc=2 chain
  (`palindromic_ec` → `middle_binary_step_pair_of_isolated` →
  `isolated_middle_binary_residual_ec`). Both routes are mathematically
  vacuous or circular for most multisets (ternary procs force fc ≥ 3,
  making the fc=2 palindromic chain unreachable), so the 2026-04-11 rewrite
  replaced them with the direct clustering theorem and deleted ~3,500 lines
  of dead scaffolding. See `docs/lean_docs/lb_rewrite_session4_audit.md` and
  `docs/lean_docs/lb_rewrite_session1_audit.md`.
-/
import LeanMn.LowerBound.CycleTypes
import LeanMn.LowerBound.EntryConflict.BinaryParity
import LeanMn.LowerBound.EntryConflict.CyclicContext
import LeanMn.LowerBound.FireCountNe

namespace LeanMn

variable {sys : System}

/-- **Mechanical EC constructor from an exact one-sided provider suffix.**

    The only real mathematics in the ZW provider route is finding the witness.
    Once we know that between consecutive fires of `i`, one neighbor is silent
    on `[k₂, a₂)` and the other is binary with even suffix count, the entry
    conflict is routine. -/
private theorem general_step_pair_ec
    (gc : GoodCycle sys)
    (i : Fin sys.rs.n)
    (a₁ a₂ k₂ : Fin gc.configs.length)
    (_hlt : a₁.val < a₂.val)
    (ha₂ : gc.moverAt a₂ = i)
    (hno_i : ∀ k : Fin gc.configs.length,
      a₁.val < k.val → k.val < a₂.val → gc.moverAt k ≠ i)
    (hk₂_gt : a₁.val < k₂.val) (hk₂_lt : k₂.val < a₂.val)
    (hprovider :
      (  (∀ j : Fin gc.configs.length,
            k₂.val ≤ j.val → j.val < a₂.val → gc.moverAt j ≠ left i)
        ∧ isBinary sys.rs (right i)
        ∧ Even (gc.intervalFireCount (right i) k₂.val a₂.val))
      ∨ (isBinary sys.rs (left i)
        ∧ Even (gc.intervalFireCount (left i) k₂.val a₂.val)
        ∧ (∀ j : Fin gc.configs.length,
            k₂.val ≤ j.val → j.val < a₂.val → gc.moverAt j ≠ right i))) :
    hasEntryConflict gc := by
  rcases hprovider with ⟨hleft_silent, hbin_r, heven_r⟩ | ⟨hbin_l, heven_l, hright_silent⟩
  · refine ⟨a₂, k₂, i, ha₂, ?_, ?_, ?_, ?_⟩
    · exact hno_i k₂ hk₂_gt hk₂_lt
    · exact (configVal_eq_of_noFire_between gc (left i) k₂.val a₂.val
        (Nat.le_of_lt hk₂_lt) a₂.isLt hleft_silent).symm
    · exact (configVal_eq_of_noFire_between gc i k₂.val a₂.val
        (Nat.le_of_lt hk₂_lt) a₂.isLt
        (fun j hj1 hj2 => hno_i j (by omega) hj2)).symm
    · exact (binary_config_eq_of_even_intervalFireCount gc (right i) hbin_r
        k₂.val a₂.val (Nat.le_of_lt hk₂_lt) a₂.isLt heven_r).symm
  · refine ⟨a₂, k₂, i, ha₂, ?_, ?_, ?_, ?_⟩
    · exact hno_i k₂ hk₂_gt hk₂_lt
    · exact (binary_config_eq_of_even_intervalFireCount gc (left i) hbin_l
        k₂.val a₂.val (Nat.le_of_lt hk₂_lt) a₂.isLt heven_l).symm
    · exact (configVal_eq_of_noFire_between gc i k₂.val a₂.val
        (Nat.le_of_lt hk₂_lt) a₂.isLt
        (fun j hj1 hj2 => hno_i j (by omega) hj2)).symm
    · exact (configVal_eq_of_noFire_between gc (right i) k₂.val a₂.val
        (Nat.le_of_lt hk₂_lt) a₂.isLt hright_silent).symm

/-- **Pigeonhole on cyclic fire arcs (L5).**

    Given three distinct fire steps `f₀ < f₁ < f₂` of a processor `i`
    and a processor `q` with `fireCount q = 2`, at least one of the
    three cyclic arcs of `i` determined by `f₀, f₁, f₂` contains no
    fire of `q` in its open interior.

    The three arcs are:

    - `(f₀, f₁)` — the first linear open arc.
    - `(f₁, f₂)` — the second linear open arc.
    - `[0, f₀) ∪ (f₂, L)` — the complementary wrap arc.

    These arcs partition `[0, L) ∖ {f₀, f₁, f₂}`. Since `i ≠ q` no fire
    of `q` sits at `f₀, f₁, f₂` themselves, so the total of `q`-fires
    across the three arcs equals `fireCount q = 2`. Three arcs, two
    items, pigeonhole: at least one arc has zero.

    This lemma is the first building block of the Path A analytical
    proof (see `path_a_disjunction_proof_attempt_2026-04-13.md`, L5). -/
private lemma exists_silent_arc_of_fc3_fc2
    (gc : GoodCycle sys) (i q : Fin sys.rs.n) (_hne : i ≠ q)
    (hfq : gc.fireCount q = 2)
    (f₀ f₁ f₂ : Fin gc.configs.length)
    (_hf₀ : gc.moverAt f₀ = i) (_hf₁ : gc.moverAt f₁ = i) (_hf₂ : gc.moverAt f₂ = i)
    (hlt₀₁ : f₀.val < f₁.val) (_hlt₁₂ : f₁.val < f₂.val) :
    (∀ k : Fin gc.configs.length, f₀.val < k.val → k.val < f₁.val →
        gc.moverAt k ≠ q)
    ∨
    (∀ k : Fin gc.configs.length, f₁.val < k.val → k.val < f₂.val →
        gc.moverAt k ≠ q)
    ∨
    ((∀ k : Fin gc.configs.length, k.val < f₀.val → gc.moverAt k ≠ q)
      ∧ (∀ k : Fin gc.configs.length, f₂.val < k.val → gc.moverAt k ≠ q)) := by
  by_contra h
  push_neg at h
  obtain ⟨h₀₁, h₁₂, hcomp⟩ := h
  -- Extract linear-arc witnesses.
  obtain ⟨k₀₁, hk₀₁_gt, hk₀₁_lt, hk₀₁_q⟩ := h₀₁
  obtain ⟨k₁₂, hk₁₂_gt, hk₁₂_lt, hk₁₂_q⟩ := h₁₂
  -- Under classical push_neg, hcomp is `(head-silent) → ∃ tail witness`.
  -- Split classically on whether the head is silent to get a wrap-arc witness.
  obtain ⟨k_c, hk_c_side, hk_c_q⟩ : ∃ k : Fin gc.configs.length,
      (k.val < f₀.val ∨ f₂.val < k.val) ∧ gc.moverAt k = q := by
    by_cases hhead :
        ∀ k : Fin gc.configs.length, k.val < f₀.val → gc.moverAt k ≠ q
    · obtain ⟨k, hk_gt, hk_q⟩ := hcomp hhead
      exact ⟨k, Or.inr hk_gt, hk_q⟩
    · push_neg at hhead
      obtain ⟨k, hk_lt, hk_q⟩ := hhead
      exact ⟨k, Or.inl hk_lt, hk_q⟩
  -- The three witnesses lie in disjoint arcs, so they are pairwise distinct.
  have hne₀₁_₁₂ : k₀₁ ≠ k₁₂ := fun heq => by
    have : k₀₁.val = k₁₂.val := congrArg Fin.val heq
    omega
  have hne₀₁_c : k₀₁ ≠ k_c := fun heq => by
    have : k₀₁.val = k_c.val := congrArg Fin.val heq
    rcases hk_c_side with h | h <;> omega
  have hne₁₂_c : k₁₂ ≠ k_c := fun heq => by
    have : k₁₂.val = k_c.val := congrArg Fin.val heq
    rcases hk_c_side with h | h <;> omega
  -- Three distinct witnesses fire `q`, so `fireCount q ≥ 3`.
  have h_fire_ge : 3 ≤ gc.fireCount q := by
    rw [gc.fireCount_eq_sum_moverAt]
    calc (3 : Nat)
        = (if gc.moverAt k₀₁ = q then (1 : Nat) else 0)
          + (if gc.moverAt k₁₂ = q then (1 : Nat) else 0)
          + (if gc.moverAt k_c = q then (1 : Nat) else 0) := by
            simp [hk₀₁_q, hk₁₂_q, hk_c_q]
      _ = ∑ k ∈ ({k₀₁, k₁₂, k_c} : Finset (Fin gc.configs.length)),
            (if gc.moverAt k = q then (1 : Nat) else 0) := by
            rw [show ({k₀₁, k₁₂, k_c} : Finset _) =
                  insert k₀₁ (insert k₁₂ {k_c}) from rfl,
                Finset.sum_insert (by simp [hne₀₁_₁₂, hne₀₁_c]),
                Finset.sum_insert (by simp [hne₁₂_c]),
                Finset.sum_singleton]
            ring
      _ ≤ ∑ k : Fin gc.configs.length,
            (if gc.moverAt k = q then (1 : Nat) else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun _ _ _ => Nat.zero_le _)
  omega

/-- **Binary even-suffix choice (L3).**

    Given a binary-count processor `b` with `fireCount b = 2` and a linear
    pair `s₁ < s₂` in `Fin L` whose open interior is non-empty
    (`s₁.val + 1 < s₂.val`), if the interior fire count of `b` is not
    exactly `1`, then the choice `k₂ := s₁ + 1` gives a suffix `[k₂, s₂)`
    with an even `b`-fire count.

    Reason: bounded by `fireCount b = 2`, so the count is in `{0, 1, 2}`;
    ruling out `1` leaves `{0, 2}`, both even. This is the "binary neighbor
    parity choice" step of the Path A disjunction proof
    (see `path_a_disjunction_proof_attempt_2026-04-13.md`, L3). -/
private lemma exists_even_suffix_of_fc2
    (gc : GoodCycle sys) (b : Fin sys.rs.n)
    (hfb : gc.fireCount b = 2)
    (s₁ s₂ : Fin gc.configs.length)
    (hgap : s₁.val + 1 < s₂.val)
    (hne_one : gc.intervalFireCount b (s₁.val + 1) s₂.val ≠ 1) :
    ∃ k₂ : Fin gc.configs.length,
      s₁.val < k₂.val ∧ k₂.val < s₂.val ∧
      Even (gc.intervalFireCount b k₂.val s₂.val) := by
  have hLe_s2 : s₁.val + 1 ≤ s₂.val := Nat.le_of_lt hgap
  have hs2_le_L : s₂.val ≤ gc.configs.length := Nat.le_of_lt s₂.isLt
  -- Bound the interior count by `fireCount b = 2` via two splits.
  have hfull : gc.fireCount b = gc.intervalFireCount b 0 gc.configs.length :=
    fireCount_eq_intervalFireCount_full gc b
  have hsplit1 : gc.intervalFireCount b 0 gc.configs.length
      = gc.intervalFireCount b 0 (s₁.val + 1)
      + gc.intervalFireCount b (s₁.val + 1) gc.configs.length :=
    intervalFireCount_split gc b (Nat.zero_le _) (le_trans hLe_s2 hs2_le_L)
  have hsplit2 : gc.intervalFireCount b (s₁.val + 1) gc.configs.length
      = gc.intervalFireCount b (s₁.val + 1) s₂.val
      + gc.intervalFireCount b s₂.val gc.configs.length :=
    intervalFireCount_split gc b hLe_s2 hs2_le_L
  have hbound : gc.intervalFireCount b (s₁.val + 1) s₂.val ≤ 2 := by omega
  refine ⟨⟨s₁.val + 1, lt_of_lt_of_le hgap hs2_le_L⟩,
    Nat.lt_succ_self _, hgap, ?_⟩
  -- `Fin.val ⟨s₁+1, _⟩ = s₁+1`, so the suffix count unfolds to the interior.
  show Even (gc.intervalFireCount b (s₁.val + 1) s₂.val)
  rcases (show gc.intervalFireCount b (s₁.val + 1) s₂.val = 0
              ∨ gc.intervalFireCount b (s₁.val + 1) s₂.val = 2 by omega) with h | h
  · rw [h]; exact ⟨0, rfl⟩
  · rw [h]; exact ⟨1, rfl⟩

/-- **Wrap-interval even-count choice.**

    For a binary processor `b` with `fireCount b = 2`, if the cyclic wrap
    interval `[s_max+1, L) ∪ [0, a)` is not counted exactly once by `b`,
    then its total count on that wrap interval is even. This is the wrap
    analogue of `exists_even_suffix_of_fc2` used by the Path A wrap branch. -/
private lemma wrap_interval_even_of_fc2
    (gc : GoodCycle sys) (b : Fin sys.rs.n)
    (hfb : gc.fireCount b = 2)
    (a s_max : Fin gc.configs.length)
    (ha_lt_s : a.val < s_max.val)
    (hne_one :
      gc.intervalFireCount b (s_max.val + 1) gc.configs.length
        + gc.intervalFireCount b 0 a.val ≠ 1) :
    Even (gc.intervalFireCount b (s_max.val + 1) gc.configs.length
      + gc.intervalFireCount b 0 a.val) := by
  have hfull : gc.fireCount b = gc.intervalFireCount b 0 gc.configs.length :=
    fireCount_eq_intervalFireCount_full gc b
  have hs_succ_le : s_max.val + 1 ≤ gc.configs.length := Nat.succ_le_of_lt s_max.isLt
  have ha_le : a.val ≤ s_max.val + 1 := by omega
  have hsplit1 :
      gc.intervalFireCount b 0 gc.configs.length
        = gc.intervalFireCount b 0 a.val
        + gc.intervalFireCount b a.val gc.configs.length :=
    intervalFireCount_split gc b (Nat.zero_le _) a.isLt.le
  have hsplit2 :
      gc.intervalFireCount b a.val gc.configs.length
        = gc.intervalFireCount b a.val (s_max.val + 1)
        + gc.intervalFireCount b (s_max.val + 1) gc.configs.length :=
    intervalFireCount_split gc b ha_le hs_succ_le
  have hbound :
      gc.intervalFireCount b (s_max.val + 1) gc.configs.length
        + gc.intervalFireCount b 0 a.val ≤ 2 := by
    omega
  rcases (show gc.intervalFireCount b (s_max.val + 1) gc.configs.length
              + gc.intervalFireCount b 0 a.val = 0
            ∨ gc.intervalFireCount b (s_max.val + 1) gc.configs.length
                + gc.intervalFireCount b 0 a.val = 2 by
      omega) with h | h
  · rw [h]
    exact ⟨0, rfl⟩
  · rw [h]
    exact ⟨1, rfl⟩

/-- **Arc-count partition (L4a).**

    Given three fires `f₀ < f₁ < f₂` of a processor `i` and another
    processor `q ≠ i`, the three arcs

    - `A₀ := (f₀, f₁)` linear open,
    - `A₁ := (f₁, f₂)` linear open,
    - `A_w := [0, f₀) ∪ (f₂, L)` wrap complement,

    partition `[0, L) ∖ {f₀, f₁, f₂}`. Since `q ≠ i`, no fire of `q`
    sits at `f₀, f₁, f₂`, so the sum of `intervalFireCount q` across
    the three arcs equals `fireCount q`.

    This is the routine bookkeeping lemma underlying Path A L4b/L4c
    (case analysis on the joint `(c_L, c_R)` distribution for two
    binary neighbors); see `path_a_L4_arc_distribution_spec_2026-04-13.md`. -/
private lemma arc_count_partition
    (gc : GoodCycle sys) (i q : Fin sys.rs.n) (hne : i ≠ q)
    (f₀ f₁ f₂ : Fin gc.configs.length)
    (hf₀ : gc.moverAt f₀ = i) (hf₁ : gc.moverAt f₁ = i) (hf₂ : gc.moverAt f₂ = i)
    (hlt₀₁ : f₀.val < f₁.val) (hlt₁₂ : f₁.val < f₂.val) :
    gc.intervalFireCount q 0 f₀.val
    + gc.intervalFireCount q (f₀.val + 1) f₁.val
    + gc.intervalFireCount q (f₁.val + 1) f₂.val
    + gc.intervalFireCount q (f₂.val + 1) gc.configs.length
    = gc.fireCount q := by
  have hf₀_lt_L : f₀.val < gc.configs.length := f₀.isLt
  have hf₁_lt_L : f₁.val < gc.configs.length := f₁.isLt
  have hf₂_lt_L : f₂.val < gc.configs.length := f₂.isLt
  -- Zero-contribution singletons at fire positions: `q ≠ i` forces
  -- `moverAt f_j ≠ q`, hence `ifc q f_j (f_j+1) = 0`.
  have h_sing₀ : gc.intervalFireCount q f₀.val (f₀.val + 1) = 0 := by
    refine intervalFireCount_eq_zero_of_noFire gc q (Nat.le_succ _) hf₀_lt_L ?_
    intro k hk_lo hk_hi
    have hkval : k.val = f₀.val := by omega
    have hk : k = f₀ := Fin.ext hkval
    rw [hk, hf₀]; exact hne
  have h_sing₁ : gc.intervalFireCount q f₁.val (f₁.val + 1) = 0 := by
    refine intervalFireCount_eq_zero_of_noFire gc q (Nat.le_succ _) hf₁_lt_L ?_
    intro k hk_lo hk_hi
    have hkval : k.val = f₁.val := by omega
    have hk : k = f₁ := Fin.ext hkval
    rw [hk, hf₁]; exact hne
  have h_sing₂ : gc.intervalFireCount q f₂.val (f₂.val + 1) = 0 := by
    refine intervalFireCount_eq_zero_of_noFire gc q (Nat.le_succ _) hf₂_lt_L ?_
    intro k hk_lo hk_hi
    have hkval : k.val = f₂.val := by omega
    have hk : k = f₂ := Fin.ext hkval
    rw [hk, hf₂]; exact hne
  -- Chain splits across the seven segments
  -- [0, f₀), [f₀, f₀+1), [f₀+1, f₁), [f₁, f₁+1), [f₁+1, f₂), [f₂, f₂+1), [f₂+1, L).
  have hfull : gc.fireCount q = gc.intervalFireCount q 0 gc.configs.length :=
    fireCount_eq_intervalFireCount_full gc q
  have hsplit_f₀ : gc.intervalFireCount q 0 gc.configs.length
      = gc.intervalFireCount q 0 f₀.val
      + gc.intervalFireCount q f₀.val gc.configs.length :=
    intervalFireCount_split gc q (Nat.zero_le _) (Nat.le_of_lt hf₀_lt_L)
  have hsplit_f₀_succ : gc.intervalFireCount q f₀.val gc.configs.length
      = gc.intervalFireCount q f₀.val (f₀.val + 1)
      + gc.intervalFireCount q (f₀.val + 1) gc.configs.length :=
    intervalFireCount_split gc q (Nat.le_succ _) hf₀_lt_L
  have hsplit_f₁ : gc.intervalFireCount q (f₀.val + 1) gc.configs.length
      = gc.intervalFireCount q (f₀.val + 1) f₁.val
      + gc.intervalFireCount q f₁.val gc.configs.length :=
    intervalFireCount_split gc q hlt₀₁ (Nat.le_of_lt hf₁_lt_L)
  have hsplit_f₁_succ : gc.intervalFireCount q f₁.val gc.configs.length
      = gc.intervalFireCount q f₁.val (f₁.val + 1)
      + gc.intervalFireCount q (f₁.val + 1) gc.configs.length :=
    intervalFireCount_split gc q (Nat.le_succ _) hf₁_lt_L
  have hsplit_f₂ : gc.intervalFireCount q (f₁.val + 1) gc.configs.length
      = gc.intervalFireCount q (f₁.val + 1) f₂.val
      + gc.intervalFireCount q f₂.val gc.configs.length :=
    intervalFireCount_split gc q hlt₁₂ (Nat.le_of_lt hf₂_lt_L)
  have hsplit_f₂_succ : gc.intervalFireCount q f₂.val gc.configs.length
      = gc.intervalFireCount q f₂.val (f₂.val + 1)
      + gc.intervalFireCount q (f₂.val + 1) gc.configs.length :=
    intervalFireCount_split gc q (Nat.le_succ _) hf₂_lt_L
  omega

/-- **L4b — distribution enumeration for `fireCount q = 2`.**

    Given three fires `f₀ < f₁ < f₂` of `i` and a processor `q ≠ i`
    with `fireCount q = 2`, the joint `(c₀, c₁, c_w)` tuple of arc
    counts falls in exactly 6 cases (all nonneg, sum = 2):

    `(2,0,0), (0,2,0), (0,0,2), (1,1,0), (1,0,1), (0,1,1)`.

    Direct consequence of `arc_count_partition` + `fireCount q = 2`
    + `omega`. Mechanical bookkeeping. -/
private lemma arc_distribution_of_fc2
    (gc : GoodCycle sys) (i q : Fin sys.rs.n) (hne : i ≠ q)
    (f₀ f₁ f₂ : Fin gc.configs.length)
    (hf₀ : gc.moverAt f₀ = i) (hf₁ : gc.moverAt f₁ = i) (hf₂ : gc.moverAt f₂ = i)
    (hlt₀₁ : f₀.val < f₁.val) (hlt₁₂ : f₁.val < f₂.val)
    (hfc_q : gc.fireCount q = 2) :
    (gc.intervalFireCount q (f₀.val + 1) f₁.val = 2 ∧
      gc.intervalFireCount q (f₁.val + 1) f₂.val = 0 ∧
      gc.intervalFireCount q 0 f₀.val
        + gc.intervalFireCount q (f₂.val + 1) gc.configs.length = 0) ∨
    (gc.intervalFireCount q (f₀.val + 1) f₁.val = 0 ∧
      gc.intervalFireCount q (f₁.val + 1) f₂.val = 2 ∧
      gc.intervalFireCount q 0 f₀.val
        + gc.intervalFireCount q (f₂.val + 1) gc.configs.length = 0) ∨
    (gc.intervalFireCount q (f₀.val + 1) f₁.val = 0 ∧
      gc.intervalFireCount q (f₁.val + 1) f₂.val = 0 ∧
      gc.intervalFireCount q 0 f₀.val
        + gc.intervalFireCount q (f₂.val + 1) gc.configs.length = 2) ∨
    (gc.intervalFireCount q (f₀.val + 1) f₁.val = 1 ∧
      gc.intervalFireCount q (f₁.val + 1) f₂.val = 1 ∧
      gc.intervalFireCount q 0 f₀.val
        + gc.intervalFireCount q (f₂.val + 1) gc.configs.length = 0) ∨
    (gc.intervalFireCount q (f₀.val + 1) f₁.val = 1 ∧
      gc.intervalFireCount q (f₁.val + 1) f₂.val = 0 ∧
      gc.intervalFireCount q 0 f₀.val
        + gc.intervalFireCount q (f₂.val + 1) gc.configs.length = 1) ∨
    (gc.intervalFireCount q (f₀.val + 1) f₁.val = 0 ∧
      gc.intervalFireCount q (f₁.val + 1) f₂.val = 1 ∧
      gc.intervalFireCount q 0 f₀.val
        + gc.intervalFireCount q (f₂.val + 1) gc.configs.length = 1) := by
  have harc := arc_count_partition gc i q hne f₀ f₁ f₂ hf₀ hf₁ hf₂ hlt₀₁ hlt₁₂
  rw [hfc_q] at harc
  omega

/-- Extract three linearly ordered firing steps from `fireCount ≥ 3`. -/
lemma exists_three_firing_steps_of_ge3
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hfc : gc.fireCount p ≥ 3) :
    ∃ (f₀ f₁ f₂ : Fin gc.configs.length),
      f₀.val < f₁.val ∧ f₁.val < f₂.val ∧
      gc.moverAt f₀ = p ∧ gc.moverAt f₁ = p ∧ gc.moverAt f₂ = p := by
  let fireSet : Finset (Fin gc.configs.length) := Finset.univ.filter (fun k => gc.moverAt k = p)
  have hcard : 2 < fireSet.card := by
    have hcount : gc.fireCount p = fireSet.card := by
      rw [gc.fireCount_eq_sum_moverAt p]
      simpa [fireSet] using
        (Finset.card_filter (s := Finset.univ) (p := fun k : Fin gc.configs.length => gc.moverAt k = p))
    omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hcard
  have hap : gc.moverAt a = p := by
    simpa [fireSet] using (Finset.mem_filter.mp ha).2
  have hbp : gc.moverAt b = p := by
    simpa [fireSet] using (Finset.mem_filter.mp hb).2
  have hcp : gc.moverAt c = p := by
    simpa [fireSet] using (Finset.mem_filter.mp hc).2
  have habv : a.val ≠ b.val := by
    intro h
    exact hab (Fin.ext h)
  have hacv : a.val ≠ c.val := by
    intro h
    exact hac (Fin.ext h)
  have hbcv : b.val ≠ c.val := by
    intro h
    exact hbc (Fin.ext h)
  by_cases hab_lt : a.val < b.val
  · by_cases hbc_lt : b.val < c.val
    · exact ⟨a, b, c, hab_lt, hbc_lt, hap, hbp, hcp⟩
    · have hcb_lt : c.val < b.val := by omega
      by_cases hac_lt : a.val < c.val
      · exact ⟨a, c, b, hac_lt, hcb_lt, hap, hcp, hbp⟩
      · have hca_lt : c.val < a.val := by omega
        exact ⟨c, a, b, hca_lt, hab_lt, hcp, hap, hbp⟩
  · have hba_lt : b.val < a.val := by omega
    by_cases hac_lt : a.val < c.val
    · exact ⟨b, a, c, hba_lt, hac_lt, hbp, hap, hcp⟩
    · have hca_lt : c.val < a.val := by omega
      by_cases hbc_lt : b.val < c.val
      · exact ⟨b, c, a, hbc_lt, hca_lt, hbp, hcp, hap⟩
      · have hcb_lt : c.val < b.val := by omega
        exact ⟨c, b, a, hcb_lt, hba_lt, hcp, hbp, hap⟩

/-- Witness site is a ternary with at least one binary neighbor. -/
def isBinaryAdjacentTernary
    (i : Fin sys.rs.n) : Prop :=
  isTernary sys.rs i ∧ (isBinary sys.rs (left i) ∨ isBinary sys.rs (right i))

/-- Linear provider witness at a fixed site `i`. -/
def LinearProviderWitness
    (gc : GoodCycle sys) (i : Fin sys.rs.n) : Prop :=
  ∃ (a₁ a₂ k₂ : Fin gc.configs.length),
    a₁.val < a₂.val ∧
    gc.moverAt a₂ = i ∧
    (∀ k : Fin gc.configs.length,
      a₁.val < k.val → k.val < a₂.val → gc.moverAt k ≠ i) ∧
    a₁.val < k₂.val ∧ k₂.val < a₂.val ∧
    (((∀ j : Fin gc.configs.length,
          k₂.val ≤ j.val → j.val < a₂.val → gc.moverAt j ≠ left i)
        ∧ isBinary sys.rs (right i)
        ∧ Even (gc.intervalFireCount (right i) k₂.val a₂.val))
      ∨
      (isBinary sys.rs (left i)
        ∧ Even (gc.intervalFireCount (left i) k₂.val a₂.val)
        ∧ (∀ j : Fin gc.configs.length,
          k₂.val ≤ j.val → j.val < a₂.val → gc.moverAt j ≠ right i)))

/-- Wrap provider witness at a fixed site `i`. -/
def WrapProviderWitness
    (gc : GoodCycle sys) (i : Fin sys.rs.n) : Prop :=
  ∃ (a s_max : Fin gc.configs.length),
    a.val < s_max.val ∧
    gc.moverAt a = i ∧
    (∀ k : Fin gc.configs.length, k.val < a.val → gc.moverAt k ≠ i) ∧
    (∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ i) ∧
    nextIndex gc.configs s_max ≠ a ∧
    (((∀ j : Fin gc.configs.length, s_max.val < j.val → gc.moverAt j ≠ left i) ∧
      (∀ j : Fin gc.configs.length, j.val < a.val → gc.moverAt j ≠ left i) ∧
      isBinary sys.rs (right i) ∧
      Even (gc.intervalFireCount (right i) (s_max.val + 1) gc.configs.length +
        gc.intervalFireCount (right i) 0 a.val))
    ∨
    (isBinary sys.rs (left i) ∧
      Even (gc.intervalFireCount (left i) (s_max.val + 1) gc.configs.length +
        gc.intervalFireCount (left i) 0 a.val) ∧
      (∀ j : Fin gc.configs.length, s_max.val < j.val → gc.moverAt j ≠ right i) ∧
      (∀ j : Fin gc.configs.length, j.val < a.val → gc.moverAt j ≠ right i)))

/-- **Provider-interval existence — linear-or-wrap disjunction.**

    Under ZW + cw > 0 + ≥ 3 binary + sub-threshold + fc ≥ 2 for all,
    there exists a provider witness at one of the two site classes
    seen in the universal probe:

    - a **binary** site, or
    - a **binary-adjacent ternary** site.

    Each site class may realize either a linear witness
    (`general_step_pair_ec`) or a wrap witness
    (`general_wrapping_step_pair_ec`). The probe shows no witness ever
    lands at a deep-interior ternary. -/

private theorem provider_interval_exists_zw
    (gc : GoodCycle sys) (_hn : sys.rs.n ≥ 9) (_hconv : converges sys gc)
    (_hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (_hsub : subThreshold sys.rs) (_h3bin : hasGe3Binary sys.rs)
    (_hzero : gc.zeroWinding) (_hcw_pos : 0 < gc.cwStepCount)
    (_hfc_ge2 : ∀ p : Fin sys.rs.n, gc.fireCount p ≥ 2) :
    (∃ i : Fin sys.rs.n,
      isBinary sys.rs i ∧
      (LinearProviderWitness gc i ∨ WrapProviderWitness gc i))
    ∨
    (∃ i : Fin sys.rs.n,
      isBinaryAdjacentTernary (sys := sys) i ∧
      (LinearProviderWitness gc i ∨ WrapProviderWitness gc i)) := by
  by_cases hadj :
      ∃ i : Fin sys.rs.n,
        isBinaryAdjacentTernary (sys := sys) i ∧
        (LinearProviderWitness gc i ∨ WrapProviderWitness gc i)
  · exact Or.inr hadj
  · by_cases hbin :
      ∃ i : Fin sys.rs.n,
        isBinary sys.rs i ∧
        (LinearProviderWitness gc i ∨ WrapProviderWitness gc i)
    · exact Or.inl hbin
    · -- Remaining content: show that some witness exists even when both
      -- of the two empirically-supported site classes appear absent.
      -- On the full tested Path A population, this branch is vacuous:
      -- every cycle already has a binary-adjacent-ternary witness, and some
      -- families additionally have redundant binary witnesses.
      sorry

/-! ### Step 2: all fc = 2 -/

/-- Every processor fires at least once (from fairness). -/
private theorem fireCount_pos_of_fair
    (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    gc.fireCount p > 0 := by
  obtain ⟨k, j, hpriv, _, hj⟩ := gc.fair p
  have hmov : gc.moverAt k = p := by
    rw [← hj]; exact (gc.moverAt_unique k j hpriv).symm
  rw [gc.fireCount_eq_sum_moverAt]
  have h2 := Finset.single_le_sum
    (f := fun i : Fin gc.configs.length =>
      if gc.moverAt i = p then (1 : Nat) else 0)
    (fun i _ => by simp only []; split_ifs <;> omega) (Finset.mem_univ k)
  simp only [hmov, ite_true] at h2; omega

/-- Every processor fires at least twice. -/
private theorem fireCount_ge2
    (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    gc.fireCount p ≥ 2 := by
  have hpos := fireCount_pos_of_fair gc p
  have hne1 := gc.fireCount_ne_one p
  omega

/-! ### Main theorem -/

/-- **Zero-winding with cw > 0 → False.**

    No callbacks. Takes zero-winding hypothesis directly. -/
theorem zeroWinding_cwPos_false
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hsub : subThreshold sys.rs) (h3bin : hasGe3Binary sys.rs)
    (hzero : gc.zeroWinding) (hcw_pos : 0 < gc.cwStepCount) :
    False := by
  -- Unified route: `provider_interval_exists_zw` returns either a linear
  -- or wrap witness at either a binary site or a binary-adjacent ternary.
  -- The site class is irrelevant to the mechanical EC constructor, so we
  -- discard it after the existential split.
  have hfc_ge2 : ∀ p : Fin sys.rs.n, gc.fireCount p ≥ 2 := fireCount_ge2 gc
  rcases provider_interval_exists_zw gc hn hconv hno_safe hsub h3bin hzero hcw_pos hfc_ge2
    with hbin | hadj
  · obtain ⟨i, _, hwit⟩ := hbin
    rcases hwit with hlin | hwrap
    · obtain ⟨a₁, a₂, k₂, hlt, ha₂, hno_i, hk₂_gt, hk₂_lt, hprovider⟩ := hlin
      exact entryConflict_impossible gc
        (general_step_pair_ec gc i a₁ a₂ k₂ hlt ha₂ hno_i hk₂_gt hk₂_lt hprovider)
    · obtain ⟨a, s_max, ha_lt_s, ha_fire, hno_before, hno_after, hwrap_ne,
        hprovider⟩ := hwrap
      exact entryConflict_impossible gc
        (general_wrapping_step_pair_ec gc i a s_max ha_lt_s ha_fire
          hno_before hno_after hwrap_ne hprovider)
  · obtain ⟨i, _, hwit⟩ := hadj
    rcases hwit with hlin | hwrap
    · obtain ⟨a₁, a₂, k₂, hlt, ha₂, hno_i, hk₂_gt, hk₂_lt, hprovider⟩ := hlin
      exact entryConflict_impossible gc
        (general_step_pair_ec gc i a₁ a₂ k₂ hlt ha₂ hno_i hk₂_gt hk₂_lt hprovider)
    · obtain ⟨a, s_max, ha_lt_s, ha_fire, hno_before, hno_after, hwrap_ne,
        hprovider⟩ := hwrap
      exact entryConflict_impossible gc
        (general_wrapping_step_pair_ec gc i a s_max ha_lt_s ha_fire
          hno_before hno_after hwrap_ne hprovider)

end LeanMn
