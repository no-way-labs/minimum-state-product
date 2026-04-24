import LeanMn.SmallN.M6Routing
import LeanMn.LowerBound.EntryConflict.PhaseExtractionBase

namespace LeanMn

variable {sys : System}

theorem normalForm_phase_neighbor_sum_pos
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hnorm : isNormalFormGap gc t phase) :
    1 ≤
      gc.intervalFireCount (left t) phase.a.val phase.s.val +
      gc.intervalFireCount (right t) phase.a.val phase.s.val := by
  set J := gc.intervalFireCount (left t) phase.a.val phase.s.val
  set K := gc.intervalFireCount (right t) phase.a.val phase.s.val
  have hconstraint := normalForm_gap_constraint gc t phase hnorm
  by_cases hJ0 : J = 0
  · have hK1 : K = 1 := hconstraint.1 hJ0
    omega
  · by_cases hK0 : K = 0
    · have hJ1 : J = 1 := hconstraint.2.1 hK0
      omega
    · have hJpos : 0 < J := Nat.pos_of_ne_zero hJ0
      have hKpos : 0 < K := Nat.pos_of_ne_zero hK0
      omega

theorem allNormal_phase_prev_is_neighbor
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall_normal : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t) :
    gc.moverAt ⟨phase.s.val - 1,
        by
          have := phase.ha_lt_s
          have := phase.s.isLt
          omega⟩ = left t ∨
      gc.moverAt ⟨phase.s.val - 1,
        by
          have := phase.ha_lt_s
          have := phase.s.isLt
          omega⟩ = right t := by
  let prev : Fin gc.configs.length := ⟨phase.s.val - 1, by
    have := phase.ha_lt_s
    have := phase.s.isLt
    omega⟩
  rcases normal_phase_has_localized_short_suffix_or_ec gc t hall_normal phase with hec | hloc
  · exact False.elim (entryConflict_impossible gc hec)
  · rcases hloc with ⟨phase1, hs, hlen1, hstart, _⟩
    have hprev_eq : phase1.a = prev := by
      have hs_val : phase1.s.val = phase.s.val := by
        simpa using congrArg Fin.val hs
      apply Fin.ext
      dsimp [prev]
      omega
    cases hstart with
    | inl hL =>
        left
        simpa [prev, hprev_eq] using hL
    | inr hR =>
        right
        simpa [prev, hprev_eq] using hR

theorem exists_binary_sandwich_allNormal_or_hasEntryConflict_of_binaryCount_ge_five
    (gc : GoodCycle sys) (hn : sys.rs.n = 6)
    (hcount : 5 ≤ binaryCount sys.rs) :
    ∃ t : Fin sys.rs.n,
      sys.rs.m (left t) = 2 ∧
      sys.rs.m (right t) = 2 ∧
      ((∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase) ∨
        hasEntryConflict gc) := by
  rcases exists_active_binary_sandwich_of_binaryCount_ge_five gc hn hcount with
    ⟨t, hbL, hbR, _⟩
  by_cases hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase
  · exact ⟨t, hbL, hbR, Or.inl hall⟩
  · push_neg at hall
    obtain ⟨phase, hmech⟩ := hall
    have hEC : hasEntryConflict gc := by
      simp only [isNormalFormGap, not_not] at hmech
      exact phase_dispatch_ec gc t phase hbL hbR hmech
    exact ⟨t, hbL, hbR, Or.inr hEC⟩

theorem exists_binary_sandwich_allNormal_of_binaryCount_ge_five
    (gc : GoodCycle sys) (hn : sys.rs.n = 6)
    (hcount : 5 ≤ binaryCount sys.rs) :
    ∃ t : Fin sys.rs.n,
      sys.rs.m (left t) = 2 ∧
      sys.rs.m (right t) = 2 ∧
      (∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase) := by
  rcases exists_binary_sandwich_allNormal_or_hasEntryConflict_of_binaryCount_ge_five gc hn hcount with
    ⟨t, hbL, hbR, hall | hEC⟩
  · exact ⟨t, hbL, hbR, hall⟩
  · exact False.elim (entryConflict_impossible gc hEC)

theorem exists_ternary_binary_sandwich_allNormal_of_binaryCount_five
    (gc : GoodCycle sys) (hn : sys.rs.n = 6)
    (hcount : binaryCount sys.rs = 5) :
    ∃ t : Fin sys.rs.n,
      sys.rs.m t ≥ 3 ∧
      sys.rs.m (left t) = 2 ∧
      sys.rs.m (right t) = 2 ∧
      (∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase) := by
  rcases exists_ternary_pivot_of_binaryCount_five sys.rs hn hcount with ⟨t, hmt, hbL, hbR⟩
  by_cases hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase
  · exact ⟨t, hmt, hbL, hbR, hall⟩
  · push_neg at hall
    obtain ⟨phase, hmech⟩ := hall
    have hEC : hasEntryConflict gc := by
      simp only [isNormalFormGap, not_not] at hmech
      exact phase_dispatch_ec gc t phase hbL hbR hmech
    exact False.elim (entryConflict_impossible gc hEC)

end LeanMn
