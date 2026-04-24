import LeanMn.SmallN.M6PhaseFront
import LeanMn.LowerBound.Proof.SafeProcessor

namespace LeanMn

def M6BinarySandwichAllNormalResidue (sys : System) : Prop :=
  ∃ gc : GoodCycle sys,
    converges sys gc ∧
    (¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q) ∧
    ∃ t : Fin sys.rs.n,
      sys.rs.m t ≥ 3 ∧
      sys.rs.m (left t) = 2 ∧
      sys.rs.m (right t) = 2 ∧
      gc.fireCount t ≥ 2 ∧
      (∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)

theorem valid_reduces_to_binary_sandwich_allNormal_of_binaryCount_ge_five
    (sys : System) (hvalid : valid sys) (hn : sys.rs.n = 6)
    (hcount : 5 ≤ binaryCount sys.rs) :
    ∃ gc : GoodCycle sys,
      converges sys gc ∧
      ∃ t : Fin sys.rs.n,
        sys.rs.m (left t) = 2 ∧
        sys.rs.m (right t) = 2 ∧
        (∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase) := by
  rcases hvalid with ⟨gc, hconv⟩
  rcases exists_binary_sandwich_allNormal_of_binaryCount_ge_five gc hn hcount with
    ⟨t, hbL, hbR, hall⟩
  exact ⟨gc, hconv, t, hbL, hbR, hall⟩

theorem valid_reduces_to_m6_binary_sandwich_allNormal_residue_of_binaryCount_five
    (sys : System) (hvalid : valid sys) (hn : sys.rs.n = 6)
    (hcount : binaryCount sys.rs = 5) :
    M6BinarySandwichAllNormalResidue sys := by
  rcases hvalid with ⟨gc, hconv⟩
  have hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q := by
    intro hsafe
    rcases hsafe with ⟨q, hq⟩
    exact safeProcessor_false (by omega : sys.rs.n ≥ 5) gc hconv q hq
  rcases exists_ternary_binary_sandwich_allNormal_of_binaryCount_five gc hn hcount with
    ⟨t, hmt, hbL, hbR, hall⟩
  have hfc_pos : 0 < gc.fireCount t := fireCount_pos_of_goodCycle gc t
  have hfc2 : gc.fireCount t ≥ 2 := fireCount_ge_2_of_pos gc t hfc_pos
  exact ⟨gc, hconv, hno_safe, t, hmt, hbL, hbR, hfc2, hall⟩

theorem valid_reduces_to_ternary_binary_sandwich_allNormal_length_ge_twelve_of_binaryCount_five
    (sys : System) (hvalid : valid sys) (hn : sys.rs.n = 6)
    (hcount : binaryCount sys.rs = 5) :
    ∃ gc : GoodCycle sys,
      converges sys gc ∧
      ∃ t : Fin sys.rs.n,
        sys.rs.m t ≥ 3 ∧
        sys.rs.m (left t) = 2 ∧
        sys.rs.m (right t) = 2 ∧
        gc.fireCount t ≥ 2 ∧
        (∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase) ∧
        12 ≤ gc.configs.length := by
  rcases valid_reduces_to_m6_binary_sandwich_allNormal_residue_of_binaryCount_five
      sys hvalid hn hcount with ⟨gc, hconv, _hno_safe, t, hmt, hbL, hbR, hfc2, hall⟩
  rcases existsUnique_nonbinary_of_binaryCount_five sys.rs hn hcount with
    ⟨u, hu, hu_unique⟩
  have hall_binary_except_t : ∀ q : Fin sys.rs.n, q ≠ t → isBinary sys.rs q := by
    intro q hqt
    by_contra hnb
    have hqu : q = u := hu_unique q hnb
    have htu : t = u := hu_unique t (by
      intro hbin
      have : sys.rs.m t = 2 := hbin
      omega)
    exact hqt (hqu.trans htu.symm)
  have hfc_ge2 : ∀ p : Fin sys.rs.n, gc.fireCount p ≥ 2 := by
    intro p
    by_cases hpt : p = t
    · simpa [hpt] using hfc2
    · have hbin : isBinary sys.rs p := hall_binary_except_t p hpt
      have hpos := fireCount_pos_of_goodCycle gc p
      exact fireCount_ge_2_of_pos gc p hpos
  have hsum := gc.sum_fireCount
  refine ⟨gc, hconv, t, hmt, hbL, hbR, hfc2, hall, ?_⟩
  have hsum_lower :
      ∑ p : Fin sys.rs.n, gc.fireCount p ≥ ∑ _p : Fin sys.rs.n, 2 := by
    exact Finset.sum_le_sum (fun p _ => hfc_ge2 p)
  have hsum_lower' : ∑ p : Fin sys.rs.n, gc.fireCount p ≥ 12 := by
    simpa [hn, Finset.sum_const, Finset.card_fin] using hsum_lower
  omega

theorem valid_reduces_to_ternary_binary_sandwich_allNormal_with_phase_of_binaryCount_five
    (sys : System) (hvalid : valid sys) (hn : sys.rs.n = 6)
    (hcount : binaryCount sys.rs = 5) :
    ∃ gc : GoodCycle sys,
      converges sys gc ∧
      ∃ t : Fin sys.rs.n,
        sys.rs.m t ≥ 3 ∧
        sys.rs.m (left t) = 2 ∧
        sys.rs.m (right t) = 2 ∧
        gc.fireCount t ≥ 2 ∧
        gc.fireCount t < gc.configs.length ∧
        (∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase) ∧
        ∃ phase : TernaryPhase gc t, True := by
  rcases valid_reduces_to_m6_binary_sandwich_allNormal_residue_of_binaryCount_five
      sys hvalid hn hcount with ⟨gc, hconv, hno_safe, t, hmt, hbL, hbR, hfc2, hall⟩
  have hfc_lt : gc.fireCount t < gc.configs.length := by
    exact fireCount_lt_length_of_hno_safe gc (by omega : sys.rs.n ≥ 5) hno_safe t
  rcases exists_ternaryPhase gc t hfc2 hfc_lt with ⟨phase, hphase⟩
  exact ⟨gc, hconv, t, hmt, hbL, hbR, hfc2, hfc_lt, hall, phase, hphase⟩

end LeanMn
