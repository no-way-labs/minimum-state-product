/-
  LowerBound/SK/PartialDet.lean — Axis C monotonicity bridge

  Establishes the "partial-det ⇒ full-det" Lean bridge motivated by the
  empirical probe R2 (2026-04-22, `axis_c_sk_extension_compat_*`):

    SK(D₁) ⊆ SK(D₂)   whenever D₂ extends D₁ pointwise.

  Concretely, if a smaller `DetDict` D₁ already witnesses a nonempty
  sink-kernel on the NonGood set, then so does every extension D₂ with
  (D₁ i l s r = some v) → (D₂ i l s r = some v).  This is the
  fix-point monotonicity direction of the iterateRemove operator under
  the partial order of `DetDict` refinements.

  The R2 probe showed that the detector fires on strictly more configs
  once we move from the cycle-only partial det to a totalizing
  extension: `SK(detOf gc) ⊊ SK(D_extension)` with ~50–74% of NG as the
  gap on the four n=9 counterexamples.  The lemmas below are the Lean
  form of the **inclusion** direction that survives that gap.
-/
import LeanMn.LowerBound.SK.SinkKernel

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LeanMn.SK

variable {sys : System}

/-- Pointwise refinement: `D₁ ≤ D₂` means every forced entry of D₁ is
    the same forced entry in D₂. -/
def DetDict.Refines (D₁ D₂ : DetDict sys) : Prop :=
  ∀ (i : Fin sys.rs.n) (l : Fin (sys.rs.m (left i)))
    (s : Fin (sys.rs.m i)) (r : Fin (sys.rs.m (right i)))
    (v : Fin (sys.rs.m i)),
    D₁ i l s r = some v → D₂ i l s r = some v

theorem DetDict.Refines.refl (D : DetDict sys) : DetDict.Refines D D :=
  fun _ _ _ _ _ h => h

theorem DetDict.Refines.trans {D₁ D₂ D₃ : DetDict sys}
    (h₁₂ : DetDict.Refines D₁ D₂) (h₂₃ : DetDict.Refines D₂ D₃) :
    DetDict.Refines D₁ D₃ :=
  fun i l s r v h => h₂₃ i l s r v (h₁₂ i l s r v h)

/-- The empty det refines every det. -/
theorem DetDict.Refines.empty (D : DetDict sys) :
    DetDict.Refines (DetDict.empty sys) D := by
  intro i l s r v h
  simp [DetDict.empty] at h

/-- `forcedOutput` is monotone under `Refines`. -/
theorem forcedOutput_mono {D₁ D₂ : DetDict sys}
    (hD : DetDict.Refines D₁ D₂) (c : Config sys.rs) (i : Fin sys.rs.n)
    (v : Fin (sys.rs.m i)) (h : forcedOutput D₁ c i = some v) :
    forcedOutput D₂ c i = some v := by
  simp only [forcedOutput] at h ⊢
  generalize hD₁ : D₁ i (c (left i)) (c i) (c (right i)) = d₁ at h
  cases d₁ with
  | none => simp at h
  | some w =>
    by_cases hw : w = c i
    · simp [hw] at h
    · simp [hw] at h
      -- h : w = v
      have hwv : w = v := h
      have hvne : ¬ v = c i := hwv ▸ hw
      have hD₂ : D₂ i (c (left i)) (c i) (c (right i)) = some w :=
        hD i (c (left i)) (c i) (c (right i)) w hD₁
      rw [hwv] at hD₂
      rw [hD₂]; simp [hvne]

/-- `forcedNeighbors` is monotone under `Refines` at the level of list
    membership: every forced successor of `D₁` is a forced successor of
    any extension `D₂`. -/
theorem forcedNeighbors_mono {D₁ D₂ : DetDict sys}
    (hD : DetDict.Refines D₁ D₂) (c c' : Config sys.rs)
    (h : c' ∈ forcedNeighbors D₁ c) :
    c' ∈ forcedNeighbors D₂ c := by
  simp only [forcedNeighbors, List.mem_filterMap] at h ⊢
  obtain ⟨i, hi_mem, hi⟩ := h
  -- hi : (match forcedOutput D₁ c i with | some v => some (applyMove c i v) | none => none) = some c'
  generalize hfo₁ : forcedOutput D₁ c i = fo at hi
  cases fo with
  | none => simp at hi
  | some v =>
    simp at hi
    have hfo₂ : forcedOutput D₂ c i = some v :=
      forcedOutput_mono hD c i v hfo₁
    refine ⟨i, hi_mem, ?_⟩
    rw [hfo₂]; simp [hi]

/-- `hasForcedNeighborIn` is monotone under `Refines` over the same
    witness set: if `D₁` has a forced neighbor of `c` in `S`, so does
    every extension `D₂`. -/
theorem hasForcedNeighborIn_mono {D₁ D₂ : DetDict sys}
    (hD : DetDict.Refines D₁ D₂) (c : Config sys.rs)
    (S : Finset (Config sys.rs))
    (h : hasForcedNeighborIn D₁ c S = true) :
    hasForcedNeighborIn D₂ c S = true := by
  simp only [hasForcedNeighborIn, List.any_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨c', hc'nbr, hc'S⟩ := h
  exact ⟨c', forcedNeighbors_mono hD c c' hc'nbr, hc'S⟩

/-- Sink-peel is monotone under `DetDict` refinement: if `D₂` refines
    `D₁` (i.e. `D₁ ≤ D₂`), then `removeOnce D₁ S ⊆ removeOnce D₂ S` on
    the **same** working set. This matches the empirical direction
    seen by R2: adding forced edges can only retain sinks. -/
theorem removeOnce_mono_det {D₁ D₂ : DetDict sys}
    (hD : DetDict.Refines D₁ D₂) (S : Finset (Config sys.rs)) :
    removeOnce D₁ S ⊆ removeOnce D₂ S := by
  intro c hc
  simp only [removeOnce, Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, hasForcedNeighborIn_mono hD c S hc.2⟩

/-- The iterate-peel is monotone under `DetDict` refinement. -/
theorem iterateRemove_mono_det {D₁ D₂ : DetDict sys}
    (hD : DetDict.Refines D₁ D₂) (S : Finset (Config sys.rs)) (n : ℕ) :
    iterateRemove D₁ S n ⊆ iterateRemove D₂ S n := by
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ k ih =>
    show removeOnce D₁ (iterateRemove D₁ S k) ⊆
         removeOnce D₂ (iterateRemove D₂ S k)
    have h1 : removeOnce D₁ (iterateRemove D₁ S k) ⊆
              removeOnce D₁ (iterateRemove D₂ S k) :=
      removeOnce_mono D₁ ih
    have h2 : removeOnce D₁ (iterateRemove D₂ S k) ⊆
              removeOnce D₂ (iterateRemove D₂ S k) :=
      removeOnce_mono_det hD _
    exact Finset.Subset.trans h1 h2

/-- **Axis C monotonicity bridge (core inclusion).**  If `D_ext`
    refines `detOf gc` (every cycle-forced entry is preserved), and the
    partial-det sink kernel `SK gc` is nonempty, then the sink kernel
    computed under `D_ext` (over the same NonGood set) is also
    nonempty.  This is the contentful direction of the Axis C empirical
    observation: the partial-det certificate `SK gc .Nonempty` survives
    every extension to a totally-defined transition rule. -/
theorem sk_ext_nonempty_of_sk_nonempty
    (gc : GoodCycle sys) {D_ext : DetDict sys}
    (hD : DetDict.Refines (detOf gc) D_ext)
    (hSK : (SK gc).Nonempty) :
    (iterateRemove D_ext
        ((Finset.univ : Finset (Config sys.rs)).filter (NonGood gc))
        (Fintype.card (Config sys.rs))).Nonempty := by
  obtain ⟨c, hc⟩ := hSK
  refine ⟨c, ?_⟩
  have := iterateRemove_mono_det hD
    ((Finset.univ : Finset (Config sys.rs)).filter (NonGood gc))
    (Fintype.card (Config sys.rs))
  exact this hc

/-- **Axis C monotonicity bridge (non-convergence form).**  If the
    partial-det certificate fires on `gc` — i.e. `SK gc .Nonempty` —
    then `gc` cannot be the good cycle of any convergent system,
    because non-convergence is already witnessed by the `SK gc`-side
    directly via `not_converges_of_SK_nonempty`. This wrapper restates
    the certificate at the point it is consumed. -/
theorem not_converges_of_partial_det_sk_nonempty
    (gc : GoodCycle sys) (hSK : (SK gc).Nonempty) :
    ¬ converges sys gc :=
  not_converges_of_SK_nonempty gc hSK

end LeanMn.SK
