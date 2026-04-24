/-
  ArcConfinement.lean

  Corrected Layer 2 infrastructure for interval displacement. The B2 probe on
  2026-04-13 showed that the "same processor at both ends" divisibility theorem
  must use the full return interval `[a₁, a₂)`, not the open interval
  `[a₁ + 1, a₂)`.
-/
import LeanMn.LowerBound.IntervalDisplacement

namespace LeanMn

variable {sys : System}

private theorem nextIndex_eq_natSucc_arc
    (gc : GoodCycle sys) {m : Nat} (hm : m + 1 < gc.configs.length) :
    nextIndex gc.configs ⟨m, lt_trans (Nat.lt_succ_self _) hm⟩ = ⟨m + 1, hm⟩ := by
  apply Fin.ext
  simp [nextIndex, Nat.mod_eq_of_lt hm]

private theorem displacementStep_modEq_nextSub (gc : GoodCycle sys)
    (k : Fin gc.configs.length) :
    gc.displacementStep k.val ≡
      (((gc.moverAt (nextIndex gc.configs k)).val : Int) - (gc.moverAt k).val)
        [ZMOD (sys.rs.n : Int)] := by
  rw [gc.displacementStep_eq_signedStep k.isLt]
  rcases gc.next_mover_is_local k with hleft | hself | hright
  · rw [hleft]
    rw [signedStep_left sys.rs.n_ge_4]
    rw [Int.modEq_iff_dvd]
    by_cases h0 : (gc.moverAt k).val = 0
    · simp [left_val, h0]
      refine ⟨1, ?_⟩
      omega
    · have hleftval : (left (gc.moverAt k)).val = (gc.moverAt k).val - 1 := by
        rw [left_val,
          show (gc.moverAt k).val + sys.rs.n - 1 = ((gc.moverAt k).val - 1) + sys.rs.n from by
            omega,
          Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hleftval]
      refine ⟨0, ?_⟩
      omega
  · rw [hself]
    rw [signedStep_self sys.rs.n_ge_4]
    simp
  · rw [hright]
    rw [signedStep_right]
    rw [Int.modEq_iff_dvd]
    by_cases htop : (gc.moverAt k).val + 1 < sys.rs.n
    · have hrightval : (right (gc.moverAt k)).val = (gc.moverAt k).val + 1 := by
        rw [right_val, Nat.mod_eq_of_lt htop]
      rw [hrightval]
      refine ⟨0, ?_⟩
      omega
    · have hlast : (gc.moverAt k).val + 1 = sys.rs.n := by omega
      have hrightval : (right (gc.moverAt k)).val = 0 := by
        simp [right_val, hlast]
      rw [hrightval]
      refine ⟨-1, ?_⟩
      omega

/-- Prefix displacement records the mover index displacement from the initial
    mover position, modulo `n`. -/
theorem GoodCycle.prefixDisplacement_modEq_start (gc : GoodCycle sys)
    (b : Nat) (hb : b < gc.configs.length) :
    gc.prefixDisplacement b ≡
      (((gc.moverAt ⟨b, hb⟩).val : Int) - (gc.moverAt ⟨0, gc.configs_length_pos⟩).val)
        [ZMOD (sys.rs.n : Int)] := by
  induction b with
  | zero =>
      have hfin : (⟨0, hb⟩ : Fin gc.configs.length) = ⟨0, gc.configs_length_pos⟩ := by
        apply Fin.ext
        simp
      simp [GoodCycle.prefixDisplacement, hfin]
  | succ b ih =>
      have hb_lt : b < gc.configs.length := by omega
      have hprefix := ih hb_lt
      have hstep :
          gc.displacementStep b ≡
            (((gc.moverAt ⟨b + 1, hb⟩).val : Int) - (gc.moverAt ⟨b, hb_lt⟩).val)
              [ZMOD (sys.rs.n : Int)] := by
        simpa [nextIndex_eq_natSucc_arc gc hb] using
          displacementStep_modEq_nextSub gc ⟨b, hb_lt⟩
      have hsum := hprefix.add hstep
      rw [gc.prefixDisplacement_succ]
      convert hsum using 1
      ring_nf

/-- Local telescoping identity for interval displacement. -/
theorem GoodCycle.intervalDisplacement_modEq_sub (gc : GoodCycle sys)
    {a b : Nat} (hab : a ≤ b) (hb : b < gc.configs.length) :
    gc.intervalDisplacement a b ≡
      (((gc.moverAt ⟨b, hb⟩).val : Int) - (gc.moverAt ⟨a, lt_of_le_of_lt hab hb⟩).val)
        [ZMOD (sys.rs.n : Int)] := by
  have hb0 := gc.prefixDisplacement_modEq_start b hb
  have ha0 := gc.prefixDisplacement_modEq_start a (lt_of_le_of_lt hab hb)
  have hsub := hb0.sub ha0
  unfold GoodCycle.intervalDisplacement
  convert hsub using 1
  ring_nf

/-- Between two occurrences of the same processor in the mover word, the full
    return interval `[a₁, a₂)` has displacement divisible by `n`. -/
theorem intervalDisplacement_between_same_proc
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (a₁ a₂ : Fin gc.configs.length)
    (hp₁ : gc.moverAt a₁ = p) (hp₂ : gc.moverAt a₂ = p)
    (hlt : a₁.val < a₂.val) :
    gc.intervalDisplacement a₁.val a₂.val ≡ 0 [ZMOD (sys.rs.n : Int)] := by
  have hmod := gc.intervalDisplacement_modEq_sub (Nat.le_of_lt hlt) a₂.isLt
  rw [hp₁, hp₂] at hmod
  simpa using hmod

/-- Classification of the corrected return interval between two fires of the same
    processor as an integral multiple of `n`. -/
theorem arc_displacement_classification
    (gc : GoodCycle sys) (b : Fin sys.rs.n)
    (_hbin : sys.rs.m b = 2)
    (a₁ a₂ : Fin gc.configs.length)
    (hb₁ : gc.moverAt a₁ = b) (hb₂ : gc.moverAt a₂ = b)
    (hlt : a₁.val < a₂.val) :
    ∃ k : Int,
      gc.intervalDisplacement a₁.val a₂.val = k * sys.rs.n := by
  have hmod := intervalDisplacement_between_same_proc gc b a₁ a₂ hb₁ hb₂ hlt
  rcases Int.modEq_zero_iff_dvd.mp hmod with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [Int.mul_comm]
  exact hk

end LeanMn
