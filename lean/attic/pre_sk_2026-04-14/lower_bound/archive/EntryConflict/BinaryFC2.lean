/-
  BinaryFC2.lean — Entry conflict infrastructure for fireCount(ri) = 2

  For 3 consecutive binary {i, ri, rri} where ri = right i fires exactly 2 times:

  Main results (all sorry-free, no axioms):

  1. `fc2_minGap_entry_conflict`: With FC(ri) = 2 and the MinFiringGap (a, b)
     having gap >= 2, if both i-firings and rri-firings in [a+1, b) are even,
     then entry conflict. This wraps minGap_parity_ec with FC=2 hypotheses.

  2. `fc2_two_gaps_same_parity`: The two gaps formed by ri's two firing steps
     partition the non-ri firings. The gap-counts for any binary neighbor have
     the SAME parity across both gaps (their sum = fireCount = even).

  3. `fc2_prefixFireCount_at_endpoints`: At ri's firing steps, i and rri
     don't change their prefix fire counts (since ri, not i/rri, fires).
-/
import LeanMn.LowerBound.EntryConflict.IsolatedParityEC

namespace LeanMn

variable {sys : System}

/-! ### Ring topology helpers -/

private theorem right_ne_self_fc2 (i : Fin sys.rs.n) : right i ≠ i := by
  intro h; have hval := congrArg Fin.val h; simp only [right_val] at hval
  have hi := i.isLt; have hn := sys.rs.n_ge_4
  by_cases hp1 : i.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt hp1] at hval; omega
  · rw [show i.val + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega

private theorem right_right_ne_right_fc2 (i : Fin sys.rs.n) :
    right (right i) ≠ right i := by
  intro h; have hval := congrArg Fin.val h; simp only [right_val] at hval
  have hi := i.isLt; have hn := sys.rs.n_ge_4
  by_cases hp1 : i.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt hp1] at hval
    by_cases hp2 : i.val + 1 + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt hp2] at hval; omega
    · rw [show i.val + 1 + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega
  · rw [show i.val + 1 = sys.rs.n from by omega, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega : 1 < sys.rs.n)] at hval; omega

/-! ### FC(ri) = 2: prefix fire count preservation at ri firing steps -/

/-- When ri fires at step k, prefixFireCount(i, k+1) = prefixFireCount(i, k).
    (Because i ≠ ri, so i doesn't fire at step k.) -/
theorem fc2_prefixFireCount_i_at_ri
    (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (k : Fin gc.configs.length) (hk : gc.moverAt k = right i) :
    gc.prefixFireCount i (k.val + 1) = gc.prefixFireCount i k.val :=
  prefixFireCount_left_preserved_at_ri_step gc i k hk

/-- When ri fires at step k, prefixFireCount(rri, k+1) = prefixFireCount(rri, k). -/
theorem fc2_prefixFireCount_rri_at_ri
    (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (k : Fin gc.configs.length) (hk : gc.moverAt k = right i) :
    gc.prefixFireCount (right (right i)) (k.val + 1) =
    gc.prefixFireCount (right (right i)) k.val :=
  prefixFireCount_right_preserved_at_ri_step gc i k hk

/-! ### Two-gap parity agreement -/

/-- Prefix fire count is monotone: pfc(a) <= pfc(b) when a <= b. -/
theorem prefixFireCount_mono (gc : GoodCycle sys) (p : Fin sys.rs.n)
    {a b : Nat} (hab : a ≤ b) (hb : b ≤ gc.configs.length) :
    gc.prefixFireCount p a ≤ gc.prefixFireCount p b := by
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0; exact Nat.le_refl _
  | succ b ih =>
    by_cases hab' : a = b + 1
    · subst hab'; exact Nat.le_refl _
    · have hab2 : a ≤ b := by omega
      have hb' : b ≤ gc.configs.length := by omega
      have ih' := ih hab2 hb'
      rw [gc.prefixFireCount_succ]
      have : gc.fireIndicator p b ≤ 1 := by
        unfold GoodCycle.fireIndicator; split_ifs <;> omega
      omega

/-- For binary processor p that is not ri: the number of p-firings in the gap
    (a, b) equals pfc(b) - pfc(a), since p doesn't fire at step a (ri fires).
    The number in the complement equals fireCount(p) - (pfc(b) - pfc(a)).
    Since fireCount(p) is even (binary), the two counts have the same parity. -/
theorem fc2_two_gaps_same_parity
    (gc : GoodCycle sys) (i : Fin sys.rs.n) (p : Fin sys.rs.n)
    (hbin_p : isBinary sys.rs p)
    (hp_ne_ri : p ≠ right i)
    (a b : Fin gc.configs.length)
    (ha : gc.moverAt a = right i) (hb : gc.moverAt b = right i)
    (hab : a.val < b.val) :
    let gap := gc.prefixFireCount p b.val - gc.prefixFireCount p a.val
    let complement := gc.fireCount p - gap
    gap % 2 = complement % 2 := by
  simp only []
  -- p ≠ ri, so p doesn't fire at steps a or b
  have hpa : gc.moverAt a ≠ p := by rw [ha]; exact fun h => hp_ne_ri h.symm
  have hpb : gc.moverAt b ≠ p := by rw [hb]; exact fun h => hp_ne_ri h.symm
  -- pfc(b) >= pfc(a) by monotonicity
  have hle : gc.prefixFireCount p a.val ≤ gc.prefixFireCount p b.val :=
    prefixFireCount_mono gc p (Nat.le_of_lt hab) (Nat.le_of_lt b.isLt)
  -- fireCount(p) is even
  have hfc_even := gc.binary_fireCount_even p hbin_p
  obtain ⟨m, hm⟩ := hfc_even
  -- gap <= fireCount(p) since pfc(b) <= pfc(L) = fireCount(p)
  have hle_fc : gc.prefixFireCount p b.val - gc.prefixFireCount p a.val ≤ gc.fireCount p := by
    have hle2 : gc.prefixFireCount p b.val ≤ gc.fireCount p :=
      prefixFireCount_mono gc p (Nat.le_of_lt b.isLt) le_rfl
    omega
  -- gap + complement = total (= even), so gap ≡ complement mod 2
  rw [hm]; omega

/-! ### MinFiringGap entry conflict for FC(ri) = 2 -/

/-- With 3 consecutive binary, FC(ri) = 2, and the MinFiringGap for ri
    having gap >= 2, if both the L-parity and R-parity conditions hold
    (i-firings and rri-firings in the gap are even), then hasEntryConflict. -/
theorem fc2_minGap_entry_conflict
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (mg : MinFiringGap gc (right i))
    (hgap2 : mg.b.val - mg.a.val ≥ 2)
    (hL_par : gc.prefixFireCount i (mg.a.val + 1) % 2 =
              gc.prefixFireCount i mg.b.val % 2)
    (hR_par : gc.prefixFireCount (right (right i)) (mg.a.val + 1) % 2 =
              gc.prefixFireCount (right (right i)) mg.b.val % 2) :
    hasEntryConflict gc :=
  minGap_parity_ec h3bin mg hgap2 hL_par hR_par

/-- Restatement: the L-parity condition for the MinFiringGap is equivalent to
    pfc(i, b) having the same parity as pfc(i, a), because pfc(a+1) = pfc(a)
    when ri fires at a. -/
theorem fc2_L_parity_iff
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (mg : MinFiringGap gc (right i)) :
    (gc.prefixFireCount i (mg.a.val + 1) % 2 = gc.prefixFireCount i mg.b.val % 2) ↔
    (gc.prefixFireCount i mg.b.val % 2 = gc.prefixFireCount i mg.a.val % 2) := by
  rw [fc2_prefixFireCount_i_at_ri gc i mg.a mg.a_fires]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Restatement: the R-parity condition is equivalent to
    pfc(rri, b) having the same parity as pfc(rri, a). -/
theorem fc2_R_parity_iff
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (mg : MinFiringGap gc (right i)) :
    (gc.prefixFireCount (right (right i)) (mg.a.val + 1) % 2 =
     gc.prefixFireCount (right (right i)) mg.b.val % 2) ↔
    (gc.prefixFireCount (right (right i)) mg.b.val % 2 =
     gc.prefixFireCount (right (right i)) mg.a.val % 2) := by
  rw [fc2_prefixFireCount_rri_at_ri gc i mg.a mg.a_fires]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-! ### All-firings-in-gap entry conflict -/

/-- If ALL of i's firings lie in the gap (a, b) — meaning pfc(i, a) = 0 and
    pfc(i, b) = fireCount(i) — then the gap's i-firings equal fireCount(i),
    which is even (binary). Similarly for rri. This gives entry conflict.

    This covers the case where the MinFiringGap (a, b) is "large enough"
    to contain all neighbor firings. -/
theorem fc2_all_firings_in_gap_ec
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (mg : MinFiringGap gc (right i))
    (hgap2 : mg.b.val - mg.a.val ≥ 2)
    (hL_all : gc.prefixFireCount i mg.a.val = 0 ∧
              gc.prefixFireCount i mg.b.val = gc.fireCount i)
    (hR_all : gc.prefixFireCount (right (right i)) mg.a.val = 0 ∧
              gc.prefixFireCount (right (right i)) mg.b.val =
              gc.fireCount (right (right i))) :
    hasEntryConflict gc := by
  apply fc2_minGap_entry_conflict h3bin mg hgap2
  · -- L-parity: pfc(a+1) = pfc(a) = 0, pfc(b) = fireCount(i) = even
    rw [fc2_prefixFireCount_i_at_ri gc i mg.a mg.a_fires, hL_all.1, hL_all.2]
    exact (Nat.even_iff.mp (gc.binary_fireCount_even i h3bin.1)).symm
  · -- R-parity: pfc(a+1) = pfc(a) = 0, pfc(b) = fireCount(rri) = even
    rw [fc2_prefixFireCount_rri_at_ri gc i mg.a mg.a_fires, hR_all.1, hR_all.2]
    exact (Nat.even_iff.mp (gc.binary_fireCount_even (right (right i)) h3bin.2.2)).symm

/-! ### FC(ri) = 2 with isolated firings: MinFiringGap construction + gap >= 2 -/

/-- FC(ri) >= 2 with isolated firings gives a MinFiringGap with gap >= 2. -/
theorem fc2_isolated_minGap_gap_ge2
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (hfc : gc.fireCount (right i) ≥ 2)
    (hiso : ∀ (a : Fin gc.configs.length),
      gc.moverAt a = right i → gc.moverAt (nextIndex gc.configs a) ≠ right i) :
    (exists_minFiringGap gc (right i) hfc).b.val -
    (exists_minFiringGap gc (right i) hfc).a.val ≥ 2 :=
  allIsolated_gap_ge2 (exists_minFiringGap gc (right i) hfc) hiso

/-! ### FC(ri) = 2: both gaps have matching parity for i -/

/-- In a MinFiringGap (a, b) for ri, the firings of i in (a, b) and the firings
    of i in the complement [0, a) ∪ (b, L) have the same parity.
    (Because i doesn't fire at a or b, so the two arcs partition all i-firings,
     and their sum = fireCount(i) = even.) -/
theorem fc2_gap_complement_parity_i
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (hbin_i : isBinary sys.rs i)
    (mg : MinFiringGap gc (right i)) :
    let gap := gc.prefixFireCount i mg.b.val - gc.prefixFireCount i mg.a.val
    let complement := gc.fireCount i - gap
    gap % 2 = complement % 2 :=
  fc2_two_gaps_same_parity gc i i hbin_i (right_ne_self_fc2 i).symm
    mg.a mg.b mg.a_fires mg.b_fires mg.a_lt_b

/-- Same for rri. -/
theorem fc2_gap_complement_parity_rri
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (hbin_rri : isBinary sys.rs (right (right i)))
    (mg : MinFiringGap gc (right i)) :
    let gap := gc.prefixFireCount (right (right i)) mg.b.val -
               gc.prefixFireCount (right (right i)) mg.a.val
    let complement := gc.fireCount (right (right i)) - gap
    gap % 2 = complement % 2 :=
  fc2_two_gaps_same_parity gc i (right (right i)) hbin_rri
    (right_right_ne_right_fc2 i) mg.a mg.b mg.a_fires mg.b_fires mg.a_lt_b

/-! ### FC(ri) = 2: the two gaps have the same parity VECTOR -/

/-- With FC(ri) = 2, let the two gaps be G₁ = (a, b) and G₂ = complement.
    The parity vector (i_parity, rri_parity) is the SAME for both gaps.
    That is: either both are EE, both are EO, both are OE, or both are OO. -/
theorem fc2_parity_vectors_agree
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (hbin_i : isBinary sys.rs i)
    (hbin_rri : isBinary sys.rs (right (right i)))
    (mg : MinFiringGap gc (right i)) :
    let gap_L := gc.prefixFireCount i mg.b.val - gc.prefixFireCount i mg.a.val
    let comp_L := gc.fireCount i - gap_L
    let gap_R := gc.prefixFireCount (right (right i)) mg.b.val -
                 gc.prefixFireCount (right (right i)) mg.a.val
    let comp_R := gc.fireCount (right (right i)) - gap_R
    (gap_L % 2 = comp_L % 2) ∧ (gap_R % 2 = comp_R % 2) :=
  ⟨fc2_gap_complement_parity_i hbin_i mg,
   fc2_gap_complement_parity_rri hbin_rri mg⟩

/-! ### Entry conflict dispatch for FC(ri) = 2 -/

/-- Combining the pieces: with 3 consecutive binary, FC(ri) >= 2, isolated firings,
    and the gap's i-firings even and rri-firings even, we get entry conflict.

    The caller must establish the even-parity hypothesis; this theorem handles
    all the MinFiringGap machinery. -/
theorem fc2_isolated_ec_of_even_gap
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (hfc : gc.fireCount (right i) ≥ 2)
    (hiso : ∀ (a : Fin gc.configs.length),
      gc.moverAt a = right i → gc.moverAt (nextIndex gc.configs a) ≠ right i)
    (heven_L : (gc.prefixFireCount i
        (exists_minFiringGap gc (right i) hfc).b.val -
      gc.prefixFireCount i
        (exists_minFiringGap gc (right i) hfc).a.val) % 2 = 0)
    (heven_R : (gc.prefixFireCount (right (right i))
        (exists_minFiringGap gc (right i) hfc).b.val -
      gc.prefixFireCount (right (right i))
        (exists_minFiringGap gc (right i) hfc).a.val) % 2 = 0) :
    hasEntryConflict gc := by
  set mg := exists_minFiringGap gc (right i) hfc
  have hgap2 := allIsolated_gap_ge2 mg hiso
  apply minGap_parity_ec h3bin mg hgap2
  · -- L-parity: pfc(a+1) % 2 = pfc(b) % 2
    rw [fc2_prefixFireCount_i_at_ri gc i mg.a mg.a_fires]
    -- Need: pfc(a) % 2 = pfc(b) % 2
    -- From heven_L: (pfc(b) - pfc(a)) % 2 = 0
    have hle := prefixFireCount_mono gc i (Nat.le_of_lt mg.a_lt_b)
      (Nat.le_of_lt mg.b.isLt)
    omega
  · -- R-parity: pfc(a+1) % 2 = pfc(b) % 2
    rw [fc2_prefixFireCount_rri_at_ri gc i mg.a mg.a_fires]
    have hle := prefixFireCount_mono gc (right (right i)) (Nat.le_of_lt mg.a_lt_b)
      (Nat.le_of_lt mg.b.isLt)
    omega

end LeanMn
