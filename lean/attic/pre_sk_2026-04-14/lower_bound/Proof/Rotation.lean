/-
  Rotation.lean — GoodCycle rotation + invariance lemmas

  The core rotation constructor `exists_rotated_goodCycle` was previously
  buried in `Archive/EntryConflict/WaterfallBridge.lean` as a private
  theorem. This file makes it a first-class piece of infrastructure for
  the 2026-04-14 rotation-invariance closure of L4d (see
  `docs/lean_docs/lb_campaign_2026-04-12/rotation_invariance_l4d_2026-04-14.md`).

  Contents:
  1. `exists_rotated_goodCycle` — ported verbatim from Archive, public.
  2. `fireCount_eq_of_rotation` — fireCount is invariant under rotation.
-/
import LeanMn.LowerBound.CycleTypes

namespace LeanMn

variable {sys : System}

/-- **Rotate a good cycle's config list by `off` positions.**

    The rotated cycle has the same configs (as a set), same length, and
    its `moverAt` is the shift-by-`off` composition with the original.

    Ported from
    `LeanMn/LowerBound/Archive/EntryConflict/WaterfallBridge.lean:246`
    (which declared this `private` and had a stale `sorry` docstring —
    the proof is complete). -/
theorem exists_rotated_goodCycle (gc : GoodCycle sys) (off : Nat) :
    ∃ gc' : GoodCycle sys,
      (∀ c : Config sys.rs, c ∈ gc'.configs ↔ c ∈ gc.configs) ∧
      gc'.configs.length = gc.configs.length ∧
      (∀ k : Fin gc'.configs.length,
        gc'.moverAt k = gc.moverAt ⟨(k.val + off) % gc.configs.length,
          Nat.mod_lt _ gc.configs_length_pos⟩) := by
  set L := gc.configs.length with hL_def
  have hLpos : 0 < L := gc.configs_length_pos
  set rotConfigs := gc.configs.rotate off with hrot_def
  have hrot_len : rotConfigs.length = L := List.length_rotate gc.configs off
  -- Helper: get on rotated list equals get on original with shifted index
  have get_rot : ∀ (k : Fin rotConfigs.length),
      rotConfigs.get k = gc.configs.get ⟨(k.val + off) % L, Nat.mod_lt _ hLpos⟩ := by
    intro k
    show (gc.configs.rotate off).get k = _
    rw [List.get_rotate]
  -- Helper: nextIndex shift identity
  have nextIdx_shift : ∀ (k : Nat), k < L →
      ((k + 1) % L + off) % L = ((k + off) % L + 1) % L := by
    intro k _
    have lhs : ((k + 1) % L + off) ≡ (k + 1 + off) [MOD L] :=
      (Nat.mod_modEq (k + 1) L).add_right off
    have rhs : ((k + off) % L + 1) ≡ (k + off + 1) [MOD L] :=
      (Nat.mod_modEq (k + off) L).add_right 1
    have : k + 1 + off = k + off + 1 := by ring
    rw [Nat.ModEq] at lhs rhs; rw [lhs, this, ← rhs]
  -- Build the rotated GoodCycle
  let gc' : GoodCycle sys := {
    configs := rotConfigs
    nonempty := by
      rw [hrot_def]; intro h; exact gc.nonempty (List.rotate_eq_nil_iff.mp h)
    unique_privileged := by
      intro c hc; exact gc.unique_privileged c (List.mem_rotate.mp hc)
    closed := by
      intro k
      set origIdx := (k.val + off) % L with horigIdx_def
      have horigIdx_lt : origIdx < L := Nat.mod_lt _ hLpos
      obtain ⟨i, hpriv, hstep⟩ := gc.closed ⟨origIdx, horigIdx_lt⟩
      refine ⟨i, ?_, ?_⟩
      · rw [get_rot k]; exact hpriv
      · rw [get_rot k]
        have hnext_eq : rotConfigs.get (nextIndex rotConfigs k) =
            gc.configs.get (nextIndex gc.configs ⟨origIdx, horigIdx_lt⟩) := by
          rw [get_rot (nextIndex rotConfigs k)]
          congr 1; ext
          simp only [nextIndex, hrot_len]
          exact nextIdx_shift k.val (hrot_len ▸ k.isLt)
        rw [hnext_eq, hstep]
    distinct := by
      intro j₁ j₂ heq
      rw [get_rot j₁, get_rot j₂] at heq
      have hinj := gc.distinct _ _ heq
      have hval_eq : (j₁.val + off) % L = (j₂.val + off) % L := Fin.val_eq_of_eq hinj
      have hj₁_lt : j₁.val < L := hrot_len ▸ j₁.isLt
      have hj₂_lt : j₂.val < L := hrot_len ▸ j₂.isLt
      ext
      exact (Nat.ModEq.add_right_cancel' off hval_eq).eq_of_lt_of_lt hj₁_lt hj₂_lt
    fair := by
      intro i
      obtain ⟨k, j0, hpriv, _, hj0⟩ := gc.fair i
      subst j0
      have hk_mem_rot : gc.configs.get k ∈ rotConfigs := by
        rw [hrot_def]
        exact (List.mem_rotate).2 (List.get_mem _ _)
      obtain ⟨k', hk'⟩ := List.mem_iff_get.mp hk_mem_rot
      set origIdx := (k'.val + off) % L with horigIdx_def
      have horigIdx_lt : origIdx < L := Nat.mod_lt _ hLpos
      obtain ⟨j, hj_priv, hj_step⟩ := gc.closed ⟨origIdx, horigIdx_lt⟩
      have hcfg_eq : gc.configs.get ⟨origIdx, horigIdx_lt⟩ = gc.configs.get k := by
        rw [← get_rot k']
        exact hk'
      have hj_priv_at_k : privileged sys (gc.configs.get k) j := by
        convert hj_priv using 1
        symm
        exact hcfg_eq
      have hnext_eq : rotConfigs.get (nextIndex rotConfigs k') =
          gc.configs.get (nextIndex gc.configs ⟨origIdx, horigIdx_lt⟩) := by
        rw [get_rot (nextIndex rotConfigs k')]
        congr 1
        ext
        simp only [nextIndex, hrot_len]
        exact nextIdx_shift k'.val (hrot_len ▸ k'.isLt)
      refine ⟨k', j, ?_, ?_, ?_⟩
      · rw [get_rot k']
        convert hj_priv using 1
      · rw [hnext_eq, get_rot k']
        exact hj_step
      · obtain ⟨u, hu_priv, hu_unique⟩ :=
          gc.unique_privileged (gc.configs.get k) (List.get_mem _ _)
        have hju : j = u := hu_unique j hj_priv_at_k
        have hiu : i = u := hu_unique i hpriv
        exact hju.trans hiu.symm
  }
  refine ⟨gc', ?_, ?_, ?_⟩
  · intro c; exact List.mem_rotate
  · exact hrot_len
  · intro k
    have hpriv := gc'.moverAt_privileged k
    change privileged sys (rotConfigs.get k) (gc'.moverAt k) at hpriv
    rw [get_rot k] at hpriv
    exact gc.moverAt_unique ⟨(k.val + off) % L, Nat.mod_lt _ hLpos⟩ (gc'.moverAt k) hpriv

/-! ### Rotation invariance lemmas

    These lemmas capture the structural properties preserved by
    `exists_rotated_goodCycle`. They are the key inputs to the
    rotation-invariance closure of L4d (see
    `docs/lean_docs/lb_campaign_2026-04-12/rotation_invariance_l4d_2026-04-14.md`). -/

/-- **Cross-length shift bijection.** Given `hlen : L' = L` with `0 < L`,
    the map `Fin L' → Fin L` sending `k ↦ (k.val + off) % L` is a
    bijection. This is the reindexing used for fireCount invariance. -/
private def shiftCrossFin (L L' : Nat) (hLpos : 0 < L) (_hlen : L' = L)
    (off : Nat) : Fin L' → Fin L :=
  fun k => ⟨(k.val + off) % L, Nat.mod_lt _ hLpos⟩

private lemma shiftCrossFin_bijective (L L' : Nat) (hLpos : 0 < L)
    (hlen : L' = L) (off : Nat) :
    Function.Bijective (shiftCrossFin L L' hLpos hlen off) := by
  refine ⟨?_, ?_⟩
  · -- Injective
    intro a b hab
    have hval : (a.val + off) % L = (b.val + off) % L :=
      Fin.val_eq_of_eq hab
    have ha_lt : a.val < L := hlen ▸ a.isLt
    have hb_lt : b.val < L := hlen ▸ b.isLt
    ext
    exact (Nat.ModEq.add_right_cancel' off hval).eq_of_lt_of_lt ha_lt hb_lt
  · -- Surjective: explicit inverse via (b + L - off % L) % L.
    intro b
    refine ⟨⟨(b.val + (L - off % L)) % L, ?_⟩, ?_⟩
    · rw [hlen]; exact Nat.mod_lt _ hLpos
    apply Fin.ext
    show ((b.val + (L - off % L)) % L + off) % L = b.val
    have h1 : (b.val + (L - off % L)) % L + off
        ≡ b.val + (L - off % L) + off [MOD L] :=
      (Nat.mod_modEq _ L).add_right off
    have h2 : b.val + (L - off % L) + off ≡ b.val [MOD L] := by
      have hkey : (L - off % L) + off ≡ 0 [MOD L] := by
        have hmod_le_off : off % L ≤ off := Nat.mod_le _ _
        have hmod_lt_L : off % L < L := Nat.mod_lt _ hLpos
        have heq : (L - off % L) + off = L + (off - off % L) := by omega
        rw [heq]
        have hdiv : off - off % L = L * (off / L) := by
          have := Nat.div_add_mod off L
          omega
        rw [hdiv]
        have : L + L * (off / L) ≡ 0 + 0 [MOD L] := by
          refine Nat.ModEq.add ?_ ?_
          · exact Nat.modEq_zero_iff_dvd.mpr (dvd_refl L)
          · exact Nat.modEq_zero_iff_dvd.mpr ⟨off / L, rfl⟩
        simpa using this
      have hadd : b.val + ((L - off % L) + off) ≡ b.val + 0 [MOD L] :=
        Nat.ModEq.refl _ |>.add hkey
      simpa [Nat.add_assoc] using hadd
    have hfin : (b.val + (L - off % L)) % L + off ≡ b.val [MOD L] :=
      h1.trans h2
    have hlt : b.val < L := b.isLt
    rw [Nat.ModEq] at hfin
    rw [hfin, Nat.mod_eq_of_lt hlt]

/-- **Lemma A: `fireCount` is invariant under rotation.**

    If `gc'` has the same length as `gc` and its `moverAt` is the
    shift-by-`off` composition with `gc.moverAt` (the defining property
    of `exists_rotated_goodCycle`), then for every processor `p`,
    `gc'.fireCount p = gc.fireCount p`. -/
theorem fireCount_eq_of_rotation
    (gc gc' : GoodCycle sys) (off : Nat)
    (hlen : gc'.configs.length = gc.configs.length)
    (hmover : ∀ k : Fin gc'.configs.length,
      gc'.moverAt k = gc.moverAt ⟨(k.val + off) % gc.configs.length,
        Nat.mod_lt _ gc.configs_length_pos⟩)
    (p : Fin sys.rs.n) :
    gc'.fireCount p = gc.fireCount p := by
  rw [gc'.fireCount_eq_sum_moverAt p, gc.fireCount_eq_sum_moverAt p]
  set L := gc.configs.length with hL_def
  have hLpos : 0 < L := gc.configs_length_pos
  -- Use the cross-length shift as a bijection Fin gc'.length → Fin L.
  exact Fintype.sum_bijective
    (shiftCrossFin L gc'.configs.length hLpos hlen off)
    (shiftCrossFin_bijective L gc'.configs.length hLpos hlen off)
    (fun k => if gc'.moverAt k = p then (1 : Nat) else 0)
    (fun k => if gc.moverAt k = p then (1 : Nat) else 0)
    (fun k => by
      show (if gc'.moverAt k = p then (1 : Nat) else 0)
          = if gc.moverAt _ = p then (1 : Nat) else 0
      rw [hmover k]
      rfl)

/-- `nextIndex` commutes with the rotation shift.

    For any `k : Fin gc'.configs.length`, applying the shift to
    `nextIndex gc'.configs k` yields the same `Fin L` element as
    applying `nextIndex gc.configs` to the shifted `k`. This is
    the core modular-arithmetic identity used by step-count
    invariance lemmas. -/
private lemma nextIndex_shift_val
    (gc gc' : GoodCycle sys)
    (hlen : gc'.configs.length = gc.configs.length)
    (off : Nat) (k : Fin gc'.configs.length) :
    ((nextIndex gc'.configs k).val + off) % gc.configs.length
      = ((k.val + off) % gc.configs.length + 1) % gc.configs.length := by
  set L := gc.configs.length with hL_def
  have hLpos : 0 < L := gc.configs_length_pos
  -- nextIndex gc'.configs k has value (k.val + 1) % gc'.configs.length
  have hnext_val : (nextIndex gc'.configs k).val = (k.val + 1) % gc'.configs.length := rfl
  rw [hnext_val]
  -- Use congrArg rather than rw to avoid motive issues with k's Fin type
  have hmod_eq : (k.val + 1) % gc'.configs.length = (k.val + 1) % L :=
    congrArg (fun n => (k.val + 1) % n) hlen
  rw [hmod_eq]
  -- Now prove ((k.val + 1) % L + off) % L = ((k.val + off) % L + 1) % L via Nat.ModEq
  have lhs_eq : ((k.val + 1) % L + off) % L = (k.val + 1 + off) % L := by
    have := (Nat.mod_modEq (k.val + 1) L).add_right off
    exact this
  have rhs_eq : ((k.val + off) % L + 1) % L = (k.val + off + 1) % L := by
    have := (Nat.mod_modEq (k.val + off) L).add_right 1
    exact this
  rw [lhs_eq, rhs_eq]
  congr 1
  ring

/-- **stepDir is equivariant under rotation.**

    `gc'.stepDir k = gc.stepDir (shift k)` where `shift` is the
    cross-length shift. This is the per-index analog of the step-count
    invariance lemmas. -/
private lemma stepDir_eq_of_rotation
    (gc gc' : GoodCycle sys)
    (hlen : gc'.configs.length = gc.configs.length) (off : Nat)
    (hmover : ∀ k : Fin gc'.configs.length,
      gc'.moverAt k = gc.moverAt ⟨(k.val + off) % gc.configs.length,
        Nat.mod_lt _ gc.configs_length_pos⟩)
    (k : Fin gc'.configs.length) :
    gc'.stepDir k = gc.stepDir
      (shiftCrossFin gc.configs.length gc'.configs.length
        gc.configs_length_pos hlen off k) := by
  set L := gc.configs.length with hL_def
  have hLpos : 0 < L := gc.configs_length_pos
  unfold GoodCycle.stepDir
  -- Unfold shiftCrossFin on the RHS
  show (let curr := gc'.moverAt k
        let nxt := gc'.moverAt (nextIndex gc'.configs k)
        if hcw : nxt = right curr then StepDir.cw
        else if hstay : nxt = curr then StepDir.stay
        else StepDir.ccw)
      = (let curr := gc.moverAt ⟨(k.val + off) % L, Nat.mod_lt _ hLpos⟩
         let nxt := gc.moverAt (nextIndex gc.configs
                                  ⟨(k.val + off) % L, Nat.mod_lt _ hLpos⟩)
         if hcw : nxt = right curr then StepDir.cw
         else if hstay : nxt = curr then StepDir.stay
         else StepDir.ccw)
  rw [hmover k]
  have hnext_eq :
      gc'.moverAt (nextIndex gc'.configs k)
        = gc.moverAt
            (nextIndex gc.configs
              ⟨(k.val + off) % L, Nat.mod_lt _ hLpos⟩) := by
    rw [hmover (nextIndex gc'.configs k)]
    congr 1
    apply Fin.ext
    have h1 := nextIndex_shift_val gc gc' hlen off k
    -- h1 : ((nextIndex gc'.configs k).val + off) % L = ((k.val + off) % L + 1) % L
    show ((nextIndex gc'.configs k).val + off) % gc.configs.length
        = (nextIndex gc.configs
              ⟨(k.val + off) % L, Nat.mod_lt _ hLpos⟩).val
    rw [h1]
    unfold nextIndex
    rfl
  rw [hnext_eq]

/-- **Lemma C1: `cwStepCount` is invariant under rotation.** -/
theorem cwStepCount_eq_of_rotation
    (gc gc' : GoodCycle sys) (off : Nat)
    (hlen : gc'.configs.length = gc.configs.length)
    (hmover : ∀ k : Fin gc'.configs.length,
      gc'.moverAt k = gc.moverAt ⟨(k.val + off) % gc.configs.length,
        Nat.mod_lt _ gc.configs_length_pos⟩) :
    gc'.cwStepCount = gc.cwStepCount := by
  unfold GoodCycle.cwStepCount
  set L := gc.configs.length with hL_def
  have hLpos : 0 < L := gc.configs_length_pos
  exact Fintype.sum_bijective
    (shiftCrossFin L gc'.configs.length hLpos hlen off)
    (shiftCrossFin_bijective L gc'.configs.length hLpos hlen off)
    (fun k => if gc'.stepDir k = StepDir.cw then (1 : Nat) else 0)
    (fun k => if gc.stepDir k = StepDir.cw then (1 : Nat) else 0)
    (fun k => by
      show (if gc'.stepDir k = StepDir.cw then (1 : Nat) else 0)
          = (if gc.stepDir _ = StepDir.cw then (1 : Nat) else 0)
      rw [stepDir_eq_of_rotation gc gc' hlen off hmover k])

/-- **Lemma C2: `ccwStepCount` is invariant under rotation.** -/
theorem ccwStepCount_eq_of_rotation
    (gc gc' : GoodCycle sys) (off : Nat)
    (hlen : gc'.configs.length = gc.configs.length)
    (hmover : ∀ k : Fin gc'.configs.length,
      gc'.moverAt k = gc.moverAt ⟨(k.val + off) % gc.configs.length,
        Nat.mod_lt _ gc.configs_length_pos⟩) :
    gc'.ccwStepCount = gc.ccwStepCount := by
  unfold GoodCycle.ccwStepCount
  set L := gc.configs.length with hL_def
  have hLpos : 0 < L := gc.configs_length_pos
  exact Fintype.sum_bijective
    (shiftCrossFin L gc'.configs.length hLpos hlen off)
    (shiftCrossFin_bijective L gc'.configs.length hLpos hlen off)
    (fun k => if gc'.stepDir k = StepDir.ccw then (1 : Nat) else 0)
    (fun k => if gc.stepDir k = StepDir.ccw then (1 : Nat) else 0)
    (fun k => by
      show (if gc'.stepDir k = StepDir.ccw then (1 : Nat) else 0)
          = (if gc.stepDir _ = StepDir.ccw then (1 : Nat) else 0)
      rw [stepDir_eq_of_rotation gc gc' hlen off hmover k])

/-- **Lemma C3: `zeroWinding` is invariant under rotation.**

    Combines `cwStepCount` and `ccwStepCount` invariance with the
    identity `totalDisplacement = cwStepCount - ccwStepCount`. -/
theorem zeroWinding_iff_of_rotation
    (gc gc' : GoodCycle sys) (off : Nat)
    (hlen : gc'.configs.length = gc.configs.length)
    (hmover : ∀ k : Fin gc'.configs.length,
      gc'.moverAt k = gc.moverAt ⟨(k.val + off) % gc.configs.length,
        Nat.mod_lt _ gc.configs_length_pos⟩) :
    gc'.zeroWinding ↔ gc.zeroWinding := by
  unfold GoodCycle.zeroWinding
  rw [gc.totalDisplacement_eq_cwStepCount_sub_ccwStepCount,
      gc'.totalDisplacement_eq_cwStepCount_sub_ccwStepCount]
  rw [cwStepCount_eq_of_rotation gc gc' off hlen hmover,
      ccwStepCount_eq_of_rotation gc gc' off hlen hmover]

/-- **Bundled rotation with invariance.**

    Convenience theorem combining `exists_rotated_goodCycle` with all
    the invariance properties (Lemmas A, C1, C2, C3). Downstream code
    (e.g. L4d closure) can destructure this in one shot instead of
    re-establishing each invariance separately. -/
theorem exists_rotated_goodCycle_invariant (gc : GoodCycle sys) (off : Nat) :
    ∃ gc' : GoodCycle sys,
      (∀ c : Config sys.rs, c ∈ gc'.configs ↔ c ∈ gc.configs) ∧
      gc'.configs.length = gc.configs.length ∧
      (∀ k : Fin gc'.configs.length,
        gc'.moverAt k = gc.moverAt ⟨(k.val + off) % gc.configs.length,
          Nat.mod_lt _ gc.configs_length_pos⟩) ∧
      (∀ p : Fin sys.rs.n, gc'.fireCount p = gc.fireCount p) ∧
      gc'.cwStepCount = gc.cwStepCount ∧
      gc'.ccwStepCount = gc.ccwStepCount ∧
      (gc'.zeroWinding ↔ gc.zeroWinding) := by
  obtain ⟨gc', hmem, hlen, hmover⟩ := exists_rotated_goodCycle gc off
  refine ⟨gc', hmem, hlen, hmover, ?_, ?_, ?_, ?_⟩
  · intro p; exact fireCount_eq_of_rotation gc gc' off hlen hmover p
  · exact cwStepCount_eq_of_rotation gc gc' off hlen hmover
  · exact ccwStepCount_eq_of_rotation gc gc' off hlen hmover
  · exact zeroWinding_iff_of_rotation gc gc' off hlen hmover

end LeanMn
