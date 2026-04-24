/-
  MirrorGoodCycle.lean — Top-level mirror GoodCycle construction

  Extracts the mirrorGoodCycle from the local construction in WaterfallBridge.lean
  (lines 1832-1910) into a reusable top-level definition. This enables the mirror
  strategy: prove left-side stubs, then derive right-side stubs via procMirror.
-/
import LeanMn.LowerBound.Archive.EntryConflict.WaterfallBridge

namespace LeanMn

variable {sys : System}

private theorem list_get_map' {α β : Type} (l : List α) (f : α → β) (i : Nat)
    (hi : i < l.length) (hi2 : i < (l.map f).length) :
    (l.map f).get ⟨i, hi2⟩ = f (l.get ⟨i, hi⟩) := by
  induction l generalizing i with
  | nil => exact absurd hi (by simp)
  | cons a rest ih =>
    match i with
    | 0 => rfl
    | i + 1 =>
      simp only [List.map, List.get]
      exact ih (i) (by simpa using hi) (by simpa using hi2)

/-- mirrorConfig is injective when n ≥ 1. -/
theorem mirrorConfig_injective (hn : sys.rs.n ≥ 1) :
    Function.Injective (mirrorConfig (rs := sys.rs)) := by
  intro c₁ c₂ heq
  funext i
  have hinv := procMirror_invol hn i
  have hfun := congrFun heq (procMirror i)
  simp only [mirrorConfig] at hfun
  suffices h : (c₁ i).val = (c₂ i).val from Fin.ext h
  have hval := congrArg Fin.val hfun
  have key : ∀ (c : Config sys.rs),
      (c (procMirror (procMirror i))).val = (c i).val :=
    fun c => congrArg (fun j => (c j).val) hinv
  rw [← key c₁, ← key c₂]; exact hval

/-- Transition function values agree under mirror. -/
theorem mirrorSystem_f_val (hn : sys.rs.n ≥ 1)
    (c : Config sys.rs) (i : Fin sys.rs.n) :
    ((mirrorSystem sys).f (procMirror i)
      (mirrorConfig c (left (procMirror i)))
      (mirrorConfig c (procMirror i))
      (mirrorConfig c (right (procMirror i)))).val =
    (sys.f i (c (left i)) (c i) (c (right i))).val := by
  have hn2 : sys.rs.n ≥ 2 := by have := sys.rs.n_ge_4; omega
  have hinv := procMirror_invol hn i
  have hleft := procMirror_left_right hn2 i
  have hright := procMirror_right_left hn2 i
  simp only [mirrorSystem, mirrorConfig]
  have hcast_val : ∀ {m₁ m₂ : Nat} (h : m₁ = m₂) (x : Fin m₁), (h ▸ x).val = x.val := by
    intro m₁ m₂ h x; cases h; rfl
  have hdep_val : ∀ (c' : Config sys.rs) {j₁ j₂ : Fin sys.rs.n} (_h : j₁ = j₂),
      (c' j₁).val = (c' j₂).val := by
    intro c' _ _ h; exact congrArg (fun j => (c' j).val) h
  have dep_f_val_eq : ∀ {j₁ j₂ : Fin sys.rs.n} (hj : j₁ = j₂)
      (L₁ : Fin (sys.rs.m (left j₁))) (S₁ : Fin (sys.rs.m j₁)) (R₁ : Fin (sys.rs.m (right j₁)))
      (L₂ : Fin (sys.rs.m (left j₂))) (S₂ : Fin (sys.rs.m j₂)) (R₂ : Fin (sys.rs.m (right j₂))),
      L₁.val = L₂.val → S₁.val = S₂.val → R₁.val = R₂.val →
      (sys.f j₁ L₁ S₁ R₁).val = (sys.f j₂ L₂ S₂ R₂).val := by
    intro j₁ j₂ hj; cases hj; intro L₁ S₁ R₁ L₂ S₂ R₂ hL hS hR
    have : L₁ = L₂ := Fin.ext hL
    have : S₁ = S₂ := Fin.ext hS
    have : R₁ = R₂ := Fin.ext hR
    subst_vars; rfl
  apply dep_f_val_eq hinv
  · rw [hcast_val, hright]
    exact hdep_val c (procMirror_invol hn (left i))
  · exact hdep_val c hinv
  · rw [hcast_val, hleft]
    exact hdep_val c (procMirror_invol hn (right i))

/-- Privileged transfers through mirror. -/
theorem privileged_mirror_iff (hn : sys.rs.n ≥ 1)
    (c : Config sys.rs) (i : Fin sys.rs.n) :
    privileged (mirrorSystem sys) (mirrorConfig c) (procMirror i) ↔
    privileged sys c i := by
  unfold privileged
  have hinv := procMirror_invol hn i
  have hs_val : (mirrorConfig c (procMirror i)).val = (c i).val := by
    simp only [mirrorConfig]
    exact congrArg (fun j => (c j).val) hinv
  constructor
  · intro hne heq
    apply hne; apply Fin.ext
    rw [mirrorSystem_f_val hn c i, congrArg Fin.val heq, hs_val]
  · intro hne heq
    apply hne; apply Fin.ext
    rw [← mirrorSystem_f_val hn c i, congrArg Fin.val heq, ← hs_val]

/-- Move transfers through mirror. -/
theorem move_mirror_eq (hn : sys.rs.n ≥ 1)
    (c : Config sys.rs) (i : Fin sys.rs.n) :
    move (mirrorSystem sys) (mirrorConfig c) (procMirror i) =
    mirrorConfig (move sys c i) := by
  funext j
  have hinv_i := procMirror_invol hn i
  have hinv_j := procMirror_invol hn j
  simp only [move, mirrorConfig]
  by_cases hj : j = procMirror i
  · have hμj : procMirror j = i := by rw [hj, hinv_i]
    rw [dif_pos hj, dif_pos hμj]
    apply Fin.ext
    simp only [Fin.val_cast]
    exact mirrorSystem_f_val hn c i
  · have hμj : procMirror j ≠ i := by
      intro heq; apply hj; rw [← hinv_j, heq, ← hinv_i, procMirror_invol hn]
    rw [dif_neg hj, dif_neg hμj]

/-- The mirrored GoodCycle: configs mapped through mirrorConfig,
    movers mapped through procMirror. -/
def mirrorGoodCycle (gc : GoodCycle sys) (hn : sys.rs.n ≥ 1) :
    GoodCycle (mirrorSystem sys) where
  configs := gc.configs.map (mirrorConfig (rs := sys.rs))
  nonempty := by simp [gc.nonempty]
  unique_privileged := by
    intro c hc
    simp at hc
    obtain ⟨c₀, hc₀_mem, hc₀_eq⟩ := hc
    subst hc₀_eq
    obtain ⟨i, hi_priv, hi_unique⟩ := gc.unique_privileged c₀ hc₀_mem
    refine ⟨procMirror i, (privileged_mirror_iff hn c₀ i).mpr hi_priv, ?_⟩
    intro j hj_priv
    let j' := procMirror j
    have hj'_eq : procMirror j' = j := procMirror_invol hn j
    rw [← hj'_eq] at hj_priv
    have hj'_priv := (privileged_mirror_iff hn c₀ j').mp hj_priv
    have hj'_eq_i := hi_unique j' hj'_priv
    rw [← hj'_eq, hj'_eq_i]
  closed := by
    intro k
    have hk_lt : k.val < gc.configs.length := by
      have := k.isLt; simp at this; exact this
    obtain ⟨i, hi_priv, hi_move⟩ := gc.closed ⟨k.val, hk_lt⟩
    refine ⟨procMirror i, ?_, ?_⟩
    · have hget : (gc.configs.map mirrorConfig).get k =
          mirrorConfig (gc.configs.get ⟨k.val, hk_lt⟩) :=
        list_get_map' gc.configs mirrorConfig k.val hk_lt (by simp; exact hk_lt)
      rw [hget]
      exact (privileged_mirror_iff hn _ i).mpr hi_priv
    · have hconfigs_m_len : (gc.configs.map mirrorConfig).length = gc.configs.length := by simp
      have hget_k : (gc.configs.map mirrorConfig).get k =
          mirrorConfig (gc.configs.get ⟨k.val, hk_lt⟩) :=
        list_get_map' gc.configs mirrorConfig k.val hk_lt (by simp; exact hk_lt)
      have hnext_val : (nextIndex (gc.configs.map mirrorConfig) k).val =
          (nextIndex gc.configs ⟨k.val, hk_lt⟩).val := by
        simp [nextIndex, hconfigs_m_len]
      have hnext_lt : (nextIndex (gc.configs.map mirrorConfig) k).val < gc.configs.length := by
        rw [hnext_val]; exact (nextIndex gc.configs ⟨k.val, hk_lt⟩).isLt
      have hget_next : (gc.configs.map mirrorConfig).get (nextIndex (gc.configs.map mirrorConfig) k) =
          mirrorConfig (gc.configs.get ⟨(nextIndex (gc.configs.map mirrorConfig) k).val, hnext_lt⟩) :=
        list_get_map' gc.configs mirrorConfig _ hnext_lt (by simp; exact hnext_lt)
      have hget_next' : gc.configs.get ⟨(nextIndex (gc.configs.map mirrorConfig) k).val, hnext_lt⟩ =
          gc.configs.get (nextIndex gc.configs ⟨k.val, hk_lt⟩) := by
        congr 1; ext; exact hnext_val
      rw [hget_next, hget_next', hi_move, hget_k, move_mirror_eq hn]
  distinct := by
    intro j₁ j₂ heq
    have hj₁_lt : j₁.val < gc.configs.length := by
      have := j₁.isLt; simp at this; exact this
    have hj₂_lt : j₂.val < gc.configs.length := by
      have := j₂.isLt; simp at this; exact this
    have hget₁ := list_get_map' gc.configs mirrorConfig j₁.val hj₁_lt (by simp; exact hj₁_lt)
    have hget₂ := list_get_map' gc.configs mirrorConfig j₂.val hj₂_lt (by simp; exact hj₂_lt)
    have heq' : mirrorConfig (gc.configs.get ⟨j₁.val, hj₁_lt⟩) =
        mirrorConfig (gc.configs.get ⟨j₂.val, hj₂_lt⟩) := by
      rw [← hget₁, ← hget₂]; exact heq
    have hinj := mirrorConfig_injective hn heq'
    have hdist := gc.distinct ⟨j₁.val, hj₁_lt⟩ ⟨j₂.val, hj₂_lt⟩ hinj
    exact Fin.ext (Fin.mk.inj hdist)
  fair := by
    intro i
    obtain ⟨k, j0, hpriv, hstep, hj0⟩ := gc.fair (procMirror i)
    subst j0
    have hk_lt : k.val < (gc.configs.map (mirrorConfig (rs := sys.rs))).length := by
      simpa using k.isLt
    let k_m : Fin (gc.configs.map (mirrorConfig (rs := sys.rs))).length := ⟨k.val, hk_lt⟩
    have hget_k : (gc.configs.map mirrorConfig).get k_m =
        mirrorConfig (gc.configs.get k) :=
      list_get_map' gc.configs mirrorConfig k.val k.isLt hk_lt
    have hconfigs_m_len : (gc.configs.map (mirrorConfig (rs := sys.rs))).length =
        gc.configs.length := by simp
    have hnext_val : (nextIndex (gc.configs.map mirrorConfig) k_m).val =
        (nextIndex gc.configs k).val := by
      simp [k_m, nextIndex, hconfigs_m_len]
    -- In the mirror, procMirror(procMirror i) = i fires at step k
    have hinv_i := procMirror_invol hn i
    refine ⟨k_m, i, ?_, ?_, rfl⟩
    · rw [hget_k]
      have := (privileged_mirror_iff hn _ (procMirror i)).mpr hpriv
      rwa [hinv_i] at this
    · have hnext_lt : (nextIndex (gc.configs.map mirrorConfig) k_m).val <
          gc.configs.length := by
        rw [hnext_val]; exact (nextIndex gc.configs k).isLt
      have hget_next := list_get_map' gc.configs mirrorConfig
        (nextIndex (gc.configs.map mirrorConfig) k_m).val hnext_lt
        (by simp; exact hnext_lt)
      have hget_next' : gc.configs.get ⟨(nextIndex (gc.configs.map mirrorConfig) k_m).val, hnext_lt⟩ =
          gc.configs.get (nextIndex gc.configs k) := by
        congr 1; ext; exact hnext_val
      rw [hget_next, hget_next', hstep, hget_k]
      conv_rhs => rw [← hinv_i]
      exact (move_mirror_eq hn _ _).symm

/-- The mirrored cycle has the same length as the original. -/
theorem mirrorGoodCycle_length (gc : GoodCycle sys) (hn : sys.rs.n ≥ 1) :
    (mirrorGoodCycle gc hn).configs.length = gc.configs.length := by
  show (gc.configs.map mirrorConfig).length = gc.configs.length
  simp

/-- Key transfer: moverAt of the mirrored cycle = procMirror of original moverAt. -/
theorem mirrorGoodCycle_moverAt (gc : GoodCycle sys) (hn : sys.rs.n ≥ 1)
    (k : Fin gc.configs.length) :
    (mirrorGoodCycle gc hn).moverAt
      ⟨k.val, (mirrorGoodCycle_length gc hn).symm ▸ k.isLt⟩ =
    procMirror (gc.moverAt k) := by
  set k' : Fin (mirrorGoodCycle gc hn).configs.length :=
    ⟨k.val, (mirrorGoodCycle_length gc hn).symm ▸ k.isLt⟩
  have hget : (mirrorGoodCycle gc hn).configs.get k' =
      mirrorConfig (gc.configs.get k) := by
    show (gc.configs.map mirrorConfig).get ⟨k.val, _⟩ = mirrorConfig (gc.configs.get k)
    exact list_get_map' gc.configs mirrorConfig k.val k.isLt _
  have hpriv : privileged (mirrorSystem sys)
      ((mirrorGoodCycle gc hn).configs.get k') (procMirror (gc.moverAt k)) := by
    rw [hget]
    exact (privileged_mirror_iff hn _ _).mpr (gc.moverAt_privileged k)
  exact (GoodCycle.moverAt_unique _ k' _ hpriv).symm

end LeanMn
