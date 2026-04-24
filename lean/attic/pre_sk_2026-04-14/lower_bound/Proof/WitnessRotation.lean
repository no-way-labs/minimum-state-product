/-
  WitnessRotation.lean — L4d closure (four-case dispatch)

  Contains the L4d closure theorem
  `l4d_no_linear_stay_both_sandwich_impossible`. The four cases are
  dispatched:

    - Case A (both no-stay): `result1_both_sandwich_stays` (Result 1).
    - Case B (proc 1 no-stay, proc 3 wrap-stay):
      `result1_prime_one_wrap_stay` (Result 1').
    - Case C (proc 1 wrap-stay, proc 3 no-stay):
      `result1_prime_one_wrap_stay_mirror`.
    - Case D (both wrap-stay): `moverAt(0)` uniqueness.

  Historical note: an earlier plan used a rotation-based approach
  (Lemma D: `exists_bAdjT_witness_iff_of_rotation`) to reduce Cases
  B/C to Result 1, but that approach hit a shape mismatch between
  `LinearProviderWitness` and `WrapProviderWitness` (see
  `docs/lean_docs/lb_campaign_2026-04-12/lemma_d_witness_rotation_proof_2026-04-14.md`).
  Result 1' replaced it with a direct slot-count argument (see
  `result1_prime_asymmetric_2026-04-14.md`).
-/
import LeanMn.LowerBound.Proof.ZeroWinding
import LeanMn.LowerBound.Proof.Rotation
import LeanMn.LowerBound.Proof.Result1

namespace LeanMn

variable {sys : System}

/-- **Case-D-of-L4d helper: wrap-stay at two sandwich-Ts is absurd.**

    `moverAt(0)` is uniquely determined, so it can't equal both
    `i₁` and `i₂` for distinct `i₁ ≠ i₂`. Used in the L4d closure
    to dispatch Case D immediately. -/
theorem l4d_case_d_both_wrap_stay
    (gc : GoodCycle sys) (i₁ i₂ : Fin sys.rs.n) (hne : i₁ ≠ i₂)
    (h₁ : gc.moverAt ⟨0, gc.configs_length_pos⟩ = i₁)
    (h₂ : gc.moverAt ⟨0, gc.configs_length_pos⟩ = i₂) :
    False :=
  hne (h₁.symm.trans h₂)

/-- **L4d closure — no-linear-stay at both sandwich-Ts is impossible.**

    Path A pivot min-CL cycles cannot have both sandwich-Ts
    simultaneously lacking a linear stay. Case analysis on the four
    joint `(hasWrapStayAt 1, hasWrapStayAt 3)` configurations:

    - **Case A** (both ¬ws): Result 1 (`result1_both_sandwich_stays`).
    - **Case B** (¬ws1, ws3): Result 1' (`result1_prime_one_wrap_stay`).
    - **Case C** (ws1, ¬ws3): Result 1' mirror.
    - **Case D** (both ws): `l4d_case_d_both_wrap_stay`. -/
theorem l4d_no_linear_stay_both_sandwich_impossible
    (gc : GoodCycle sys)
    (hpivot : isPivotFamily sys.rs)
    (hne_1_3 : (⟨1, by have := hpivot.1; omega⟩ : Fin sys.rs.n)
              ≠ ⟨3, by have := hpivot.1; omega⟩)
    (hfc1 : gc.fireCount ⟨1, by have := hpivot.1; omega⟩ = 3)
    (hfc3 : gc.fireCount ⟨3, by have := hpivot.1; omega⟩ = 3)
    (hfc0 : gc.fireCount ⟨0, by have := hpivot.1; omega⟩ = 2)
    (hfc2 : gc.fireCount ⟨2, by have := hpivot.1; omega⟩ = 2)
    (hfc4 : gc.fireCount ⟨4, by have := hpivot.1; omega⟩ = 2)
    (hnls_1 : ¬ gc.hasLinearStayAt ⟨1, by have := hpivot.1; omega⟩)
    (hnls_3 : ¬ gc.hasLinearStayAt ⟨3, by have := hpivot.1; omega⟩) :
    False := by
  -- Case split on whether each sandwich-T has a wrap stay.
  by_cases hws1 : gc.hasWrapStayAt ⟨1, by have := hpivot.1; omega⟩
  · by_cases hws3 : gc.hasWrapStayAt ⟨3, by have := hpivot.1; omega⟩
    · -- Case D: both wrap-stay → moverAt 0 = 1 AND moverAt 0 = 3.
      exact l4d_case_d_both_wrap_stay gc _ _ hne_1_3 hws1.2 hws3.2
    · -- Case C: i=1 wrap-stay, i=3 no-stay. Apply Result 1' mirror.
      have hns3 : ¬ gc.hasStayAt ⟨3, by have := hpivot.1; omega⟩ := by
        intro h
        rcases h with hlin | hwrap
        · exact hnls_3 hlin
        · exact hws3 hwrap
      exact result1_prime_one_wrap_stay_mirror gc hpivot hfc1 hfc3 hfc0 hfc2 hfc4
        hws1 hnls_1 hns3
  · by_cases hws3 : gc.hasWrapStayAt ⟨3, by have := hpivot.1; omega⟩
    · -- Case B: i=1 no-stay, i=3 wrap-stay. Apply Result 1'.
      have hns1 : ¬ gc.hasStayAt ⟨1, by have := hpivot.1; omega⟩ := by
        intro h
        rcases h with hlin | hwrap
        · exact hnls_1 hlin
        · exact hws1 hwrap
      exact result1_prime_one_wrap_stay gc hpivot hfc1 hfc3 hfc0 hfc2 hfc4
        hns1 hws3 hnls_3
    · -- Case A: both no-linear-stay AND no-wrap-stay = both no-stay.
      -- Apply Result 1.
      have hns1 : ¬ gc.hasStayAt ⟨1, by have := hpivot.1; omega⟩ := by
        intro h
        rcases h with hlin | hwrap
        · exact hnls_1 hlin
        · exact hws1 hwrap
      have hns3 : ¬ gc.hasStayAt ⟨3, by have := hpivot.1; omega⟩ := by
        intro h
        rcases h with hlin | hwrap
        · exact hnls_3 hlin
        · exact hws3 hwrap
      exact result1_both_sandwich_stays gc hpivot hfc1 hfc3 hfc0 hfc2 hfc4
        ⟨hns1, hns3⟩

end LeanMn
