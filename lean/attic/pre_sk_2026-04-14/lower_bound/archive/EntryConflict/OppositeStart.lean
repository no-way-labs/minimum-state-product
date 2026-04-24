/-
  OppositeStart.lean — Entry conflict from opposite-start gaps (FC(p) = 2)

  For 3 consecutive binary {i, p = right i, rri = right(right i)} where p
  fires exactly 2 times at steps a and b (MinFiringGap), the cycle is
  partitioned into two gaps:
    Gap1 = (a, b)   — steps a+1 .. b-1
    Gap2 = complement — steps b+1 .. a-1 (wrapping)

  If the gaps start on OPPOSITE sides (gap1's first mover is i = left(p),
  gap2's first mover is rri = right(p)), then:
  - rri is frozen in gap1 (fires 0 times) — from one-sided confinement
  - i is frozen in gap2 (fires 0 times) — from one-sided confinement
  These frozen conditions force both neighbors' gap-firings to be even,
  which gives entry conflict at p.

  Main results (all sorry-free, no axioms):

  1. `frozen_in_gap_even_parity`: binary neighbor frozen in gap → even parity.
  2. `all_firings_in_gap_even_parity`: all firings of binary neighbor in gap → even.
  3. `opposite_start_entry_conflict`: frozen rri in gap + frozen i outside → EC.
  4. `fc2_opposite_start_ec`: FC(p) = 2 + opposite starts → EC.
  5. `fc2_opposite_start_ec_v2`: symmetric version (gap starts right, complement left).
-/
import LeanMn.LowerBound.Archive.EntryConflict.BinaryFC2

namespace LeanMn

variable {sys : System}

/-! ### Ring topology helpers -/

private theorem i_ne_ri (i : Fin sys.rs.n) : i ≠ right i := by
  intro h; have hval := congrArg Fin.val h; simp only [right_val] at hval
  have hi := i.isLt; have hn := sys.rs.n_ge_4
  by_cases hp1 : i.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt hp1] at hval; omega
  · rw [show i.val + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega

private theorem rri_ne_ri (i : Fin sys.rs.n) : right (right i) ≠ right i := by
  intro h; have hval := congrArg Fin.val h; simp only [right_val] at hval
  have hi := i.isLt; have hn := sys.rs.n_ge_4
  by_cases hp1 : i.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt hp1] at hval
    by_cases hp2 : i.val + 1 + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt hp2] at hval; omega
    · rw [show i.val + 1 + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega
  · rw [show i.val + 1 = sys.rs.n from by omega, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega : 1 < sys.rs.n)] at hval; omega

/-! ### Frozen-in-gap gives even parity -/

/-- If binary neighbor q never fires in the MinFiringGap (a, b), then the
    prefix fire count change in the gap is 0, hence even.

    Specifically: pfc(q, a+1) % 2 = pfc(q, b) % 2, because both equal pfc(q, a). -/
theorem frozen_in_gap_even_parity
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p) (q : Fin sys.rs.n)
    (hq_ne_p : q ≠ p)
    (hq_frozen : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ q) :
    gc.prefixFireCount q (mg.a.val + 1) % 2 =
    gc.prefixFireCount q mg.b.val % 2 := by
  -- q doesn't fire at step a (p fires at a, and q ≠ p)
  have hq_not_at_a : gc.moverAt mg.a ≠ q := by rw [mg.a_fires]; exact hq_ne_p.symm
  -- pfc(q, a+1) = pfc(q, a) since q doesn't fire at step a
  have h1 := prefixFireCount_step_ne gc q mg.a.val mg.a.isLt hq_not_at_a
  -- pfc(q, b) = pfc(q, a+1) since q doesn't fire in (a, b)
  have h2 := prefixFireCount_eq_of_noFire_range gc q (mg.a.val + 1) mg.b.val
    (by have := mg.a_lt_b; omega) (Nat.le_of_lt mg.b.isLt)
    (fun k hk1 hk2 => hq_frozen k (by omega) hk2)
  -- pfc(q, a+1) = pfc(q, a), pfc(q, b) = pfc(q, a+1)
  -- So pfc(q, a+1) = pfc(q, b)
  omega

/-- If a binary neighbor q fires 0 times outside the MinFiringGap (a, b),
    then all of q's firings occur in the gap: the count in the gap equals
    fireCount(q), which is even. Hence pfc(q, a+1) % 2 = pfc(q, b) % 2.

    "Outside the gap" means: steps [0, a] ∪ [b, L).
    Since q ≠ p, q doesn't fire at step a. So q fires 0 times in [0, a).
    And q fires 0 times in [b, L). Total = 0. Hence gap count = fireCount(q). -/
theorem all_firings_in_gap_even_parity
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p) (q : Fin sys.rs.n)
    (hbin_q : isBinary sys.rs q)
    (hq_ne_p : q ≠ p)
    -- q doesn't fire at any step outside the open interval (a, b):
    (hq_frozen_before : ∀ k : Fin gc.configs.length,
      k.val ≤ mg.a.val → gc.moverAt k ≠ q)
    (hq_frozen_after : ∀ k : Fin gc.configs.length,
      mg.b.val ≤ k.val → gc.moverAt k ≠ q) :
    gc.prefixFireCount q (mg.a.val + 1) % 2 =
    gc.prefixFireCount q mg.b.val % 2 := by
  -- pfc(q, a+1) = pfc(q, a) since q ≠ p and p fires at a
  have hq_not_at_a : gc.moverAt mg.a ≠ q := by rw [mg.a_fires]; exact hq_ne_p.symm
  have h_a1_eq_a := prefixFireCount_step_ne gc q mg.a.val mg.a.isLt hq_not_at_a
  -- pfc(q, a) = pfc(q, 0) = 0 since q doesn't fire in [0, a)
  have h_a_eq_0 : gc.prefixFireCount q mg.a.val = gc.prefixFireCount q 0 :=
    prefixFireCount_eq_of_noFire_range gc q 0 mg.a.val (Nat.zero_le _)
      (Nat.le_of_lt mg.a.isLt)
      (fun k hk1 hk2 => hq_frozen_before k (by omega))
  have h_pfc0 : gc.prefixFireCount q 0 = 0 := gc.prefixFireCount_zero q
  -- pfc(q, L) = pfc(q, b) since q doesn't fire in [b, L)
  have h_L_eq_b : gc.prefixFireCount q gc.configs.length = gc.prefixFireCount q mg.b.val :=
    prefixFireCount_eq_of_noFire_range gc q mg.b.val gc.configs.length
      (Nat.le_of_lt mg.b.isLt) le_rfl
      (fun k hk1 hk2 => hq_frozen_after k (by omega))
  -- fireCount(q) = pfc(q, L) = pfc(q, b). And pfc(q, a+1) = 0.
  -- So gap count = pfc(q, b) - pfc(q, a+1) = pfc(q, b) - 0 = pfc(q, b) = fireCount(q).
  -- fireCount(q) is even.
  have hfc_even := gc.binary_fireCount_even q hbin_q
  obtain ⟨m, hm⟩ := hfc_even
  -- pfc(q, a+1) = 0
  have h_a1_zero : gc.prefixFireCount q (mg.a.val + 1) = 0 := by
    rw [h_a1_eq_a, h_a_eq_0, h_pfc0]
  -- pfc(q, b) = fireCount(q) = 2*m
  have h_b_val : gc.prefixFireCount q mg.b.val = 2 * m := by
    have : gc.fireCount q = gc.prefixFireCount q gc.configs.length := rfl
    rw [hm] at this; omega
  rw [h_a1_zero, h_b_val]; omega

/-! ### Opposite-start entry conflict -/

/-- **Opposite-start entry conflict.**

    With 3 consecutive binary {i, p = right i, rri = right(right i)},
    a MinFiringGap for p with gap >= 2, and:
    - rri never fires in the gap (frozen in gap)
    - i never fires outside the gap (frozen outside gap)
    Then: hasEntryConflict.

    Proof: rri frozen in gap → R-parity even.
    i frozen outside → all i-firings in gap = fireCount(i) = even → L-parity even.
    Both even → `minGap_parity_ec` gives entry conflict. -/
theorem opposite_start_entry_conflict
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (mg : MinFiringGap gc (right i))
    (hgap2 : mg.b.val - mg.a.val ≥ 2)
    -- rri = right(right i) never fires in the gap (a, b):
    (hR_frozen_in_gap : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ right (right i))
    -- i never fires outside the gap:
    (hL_frozen_before : ∀ k : Fin gc.configs.length,
      k.val ≤ mg.a.val → gc.moverAt k ≠ i)
    (hL_frozen_after : ∀ k : Fin gc.configs.length,
      mg.b.val ≤ k.val → gc.moverAt k ≠ i) :
    hasEntryConflict gc := by
  apply minGap_parity_ec h3bin mg hgap2
  · -- L-parity: all of i's firings are in the gap → even
    exact all_firings_in_gap_even_parity mg i h3bin.1 (i_ne_ri i) hL_frozen_before hL_frozen_after
  · -- R-parity: rri frozen in gap → 0 firings in gap → even
    exact frozen_in_gap_even_parity mg (right (right i)) (rri_ne_ri i) hR_frozen_in_gap

/-- **Symmetric version: right-start gap, left-start complement.**

    With 3 consecutive binary, MinFiringGap for p = right i, gap >= 2, and:
    - i never fires in the gap (frozen in gap)
    - rri never fires outside the gap (frozen outside gap)
    Then: hasEntryConflict. -/
theorem opposite_start_entry_conflict_sym
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (mg : MinFiringGap gc (right i))
    (hgap2 : mg.b.val - mg.a.val ≥ 2)
    -- i never fires in the gap (a, b):
    (hL_frozen_in_gap : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ i)
    -- rri never fires outside the gap:
    (hR_frozen_before : ∀ k : Fin gc.configs.length,
      k.val ≤ mg.a.val → gc.moverAt k ≠ right (right i))
    (hR_frozen_after : ∀ k : Fin gc.configs.length,
      mg.b.val ≤ k.val → gc.moverAt k ≠ right (right i)) :
    hasEntryConflict gc := by
  apply minGap_parity_ec h3bin mg hgap2
  · -- L-parity: i frozen in gap → 0 firings → even
    exact frozen_in_gap_even_parity mg i (i_ne_ri i) hL_frozen_in_gap
  · -- R-parity: all of rri's firings are in the gap → even
    exact all_firings_in_gap_even_parity mg (right (right i)) h3bin.2.2 (rri_ne_ri i)
      hR_frozen_before hR_frozen_after

/-! ### FC(p) = 2: opposite-start assembly -/

/-- **FC(p) = 2: opposite-start gives entry conflict.**

    When p = right(i) fires exactly 2 times with isolated firings,
    the MinFiringGap (a, b) and its complement form two gaps.
    If the first mover in the gap is i (left) and
    i never fires outside the gap (i.e., the complement's movers are
    on the right side, freezing i):
    rri is frozen in the gap by the one-sided confinement.
    This gives entry conflict.

    The hypotheses about frozen positions are what the caller must establish
    from the one-sided confinement argument. -/
theorem fc2_opposite_start_ec
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (hfc : gc.fireCount (right i) ≥ 2)
    (hiso : ∀ (a : Fin gc.configs.length),
      gc.moverAt a = right i → gc.moverAt (nextIndex gc.configs a) ≠ right i)
    -- rri never fires in the gap:
    (hR_frozen : let mg := exists_minFiringGap gc (right i) hfc
      ∀ k : Fin gc.configs.length,
        mg.a.val < k.val → k.val < mg.b.val →
        gc.moverAt k ≠ right (right i))
    -- i never fires outside the gap:
    (hL_frozen_before : let mg := exists_minFiringGap gc (right i) hfc
      ∀ k : Fin gc.configs.length,
        k.val ≤ mg.a.val → gc.moverAt k ≠ i)
    (hL_frozen_after : let mg := exists_minFiringGap gc (right i) hfc
      ∀ k : Fin gc.configs.length,
        mg.b.val ≤ k.val → gc.moverAt k ≠ i) :
    hasEntryConflict gc := by
  set mg := exists_minFiringGap gc (right i) hfc
  have hgap2 := allIsolated_gap_ge2 mg hiso
  exact opposite_start_entry_conflict h3bin mg hgap2 hR_frozen hL_frozen_before hL_frozen_after

/-! ### Both-even entry conflict (direct parity version) -/

/-- **Both-even entry conflict.**

    The most general parity-based entry conflict for MinFiringGap:
    if i fires an even number of times in the gap AND rri fires an
    even number of times in the gap, then entry conflict.

    This subsumes opposite_start_entry_conflict (where even comes from
    0 or fireCount) and fc2_minGap_entry_conflict. -/
theorem both_even_gap_ec
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (mg : MinFiringGap gc (right i))
    (hgap2 : mg.b.val - mg.a.val ≥ 2)
    (hL_even : (gc.prefixFireCount i mg.b.val -
                gc.prefixFireCount i (mg.a.val + 1)) % 2 = 0)
    (hR_even : (gc.prefixFireCount (right (right i)) mg.b.val -
                gc.prefixFireCount (right (right i)) (mg.a.val + 1)) % 2 = 0) :
    hasEntryConflict gc := by
  apply minGap_parity_ec h3bin mg hgap2
  · -- L-parity: pfc(i, a+1) % 2 = pfc(i, b) % 2
    -- From hL_even: (pfc(b) - pfc(a+1)) % 2 = 0
    have hle := prefixFireCount_mono gc i
      (show mg.a.val + 1 ≤ mg.b.val by have := mg.a_lt_b; omega)
      (Nat.le_of_lt mg.b.isLt)
    omega
  · -- R-parity
    have hle := prefixFireCount_mono gc (right (right i))
      (show mg.a.val + 1 ≤ mg.b.val by have := mg.a_lt_b; omega)
      (Nat.le_of_lt mg.b.isLt)
    omega

/-! ### FC = 2 frozen complement: entry conflict from complement-frozen neighbor -/

/-- When FC(p) = 2 with 3 consecutive binary and isolated firings:
    if one binary neighbor fires 0 times in the gap and the other fires
    0 times in the complement, then entry conflict.

    This directly handles the opposite-start scenario where gap1 confines
    movers to one side (freezing the far neighbor in the gap) and gap2
    confines movers to the other side (freezing the near neighbor in the
    complement, meaning all its firings are in the gap = even). -/
theorem fc2_frozen_both_sides_ec
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (mg : MinFiringGap gc (right i))
    (hgap2 : mg.b.val - mg.a.val ≥ 2)
    -- rri fires 0 times in the gap:
    (hR_zero_in_gap : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ right (right i))
    -- i fires 0 times in [0, a] and [b, L):
    (hL_zero_before : ∀ k : Fin gc.configs.length,
      k.val ≤ mg.a.val → gc.moverAt k ≠ i)
    (hL_zero_after : ∀ k : Fin gc.configs.length,
      mg.b.val ≤ k.val → gc.moverAt k ≠ i) :
    hasEntryConflict gc :=
  opposite_start_entry_conflict h3bin mg hgap2 hR_zero_in_gap hL_zero_before hL_zero_after

/-- Symmetric: i fires 0 in gap, rri fires 0 outside. -/
theorem fc2_frozen_both_sides_ec_sym
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (mg : MinFiringGap gc (right i))
    (hgap2 : mg.b.val - mg.a.val ≥ 2)
    -- i fires 0 times in the gap:
    (hL_zero_in_gap : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ i)
    -- rri fires 0 times in [0, a] and [b, L):
    (hR_zero_before : ∀ k : Fin gc.configs.length,
      k.val ≤ mg.a.val → gc.moverAt k ≠ right (right i))
    (hR_zero_after : ∀ k : Fin gc.configs.length,
      mg.b.val ≤ k.val → gc.moverAt k ≠ right (right i)) :
    hasEntryConflict gc :=
  opposite_start_entry_conflict_sym h3bin mg hgap2 hL_zero_in_gap hR_zero_before hR_zero_after

/-! ### One-gap-frozen sufficiency -/

/-- **One neighbor frozen in gap suffices when the other is frozen in complement.**

    This is the topmost assembly lemma: given ANY MinFiringGap for
    p = right(i) with gap ≥ 2, if we can establish that one neighbor
    is frozen in the gap and the other is frozen in the complement,
    we immediately get entry conflict. No need for FC = 2.

    The two "frozen" hypotheses encode the opposite-start confinement. -/
theorem one_frozen_each_side_ec
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (mg : MinFiringGap gc (right i))
    (hgap2 : mg.b.val - mg.a.val ≥ 2)
    -- One of the two cross-frozen patterns:
    (hfrozen : (-- Pattern A: rri frozen in gap, i frozen in complement
                (∀ k : Fin gc.configs.length,
                  mg.a.val < k.val → k.val < mg.b.val →
                  gc.moverAt k ≠ right (right i)) ∧
                (∀ k : Fin gc.configs.length,
                  k.val ≤ mg.a.val → gc.moverAt k ≠ i) ∧
                (∀ k : Fin gc.configs.length,
                  mg.b.val ≤ k.val → gc.moverAt k ≠ i))
              ∨
               -- Pattern B: i frozen in gap, rri frozen in complement
               ((∀ k : Fin gc.configs.length,
                  mg.a.val < k.val → k.val < mg.b.val →
                  gc.moverAt k ≠ i) ∧
                (∀ k : Fin gc.configs.length,
                  k.val ≤ mg.a.val → gc.moverAt k ≠ right (right i)) ∧
                (∀ k : Fin gc.configs.length,
                  mg.b.val ≤ k.val → gc.moverAt k ≠ right (right i)))) :
    hasEntryConflict gc := by
  rcases hfrozen with ⟨hR, hLb, hLa⟩ | ⟨hL, hRb, hRa⟩
  · exact opposite_start_entry_conflict h3bin mg hgap2 hR hLb hLa
  · exact opposite_start_entry_conflict_sym h3bin mg hgap2 hL hRb hRa

end LeanMn
