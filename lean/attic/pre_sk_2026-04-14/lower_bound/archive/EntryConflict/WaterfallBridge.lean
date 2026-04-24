/-
  WaterfallBridge.lean — Convergence transfer, rotation, relabeling, waterfall construction

  Bridges from uniform CW/CCW good cycles to waterfall cycles and shadow theorem.
  Includes value relabeling, proc-index mirroring, and the
  uniform_fullSupport_pivot_false theorem.
-/
import LeanMn.LowerBound.EntryConflict.PhaseExtractionBase

namespace LeanMn

variable {sys : System}

/-! ### Step 6a: Canonical gap backtracking → BAFArcAdj → entry conflict

  The key new math for closing the lower bound.

  **Setup:** Pivot t (ternary) with binary left(t) and right(t), all procs
  fire (full support), fireCount t = 2 giving two canonical gaps, each with
  (J,K) = (1,1). Both canonical gaps launch toward the same neighbor
  (same-start case; opposite-start is closed by frozen-neighbor parity).

  **Each canonical (1,1) gap** is a walk from one binary neighbor of t to
  the other, with t absent:
  - The unique left(t) fire is the first mover of the gap.
  - The unique right(t) fire is at step s − 1 (adjacent to the t-fire at s).
  - The walk goes from left(t) along the outside arc to right(t).

  **Backtracking → BAFArcAdj → False:**
  If the outside-arc walk backtracks (changes direction), take the first
  backtrack point j. This creates a BAFArcAdj structure:
  - proc = j (the processor where the backtrack occurs)
  - cwProcStep, cwNeighborStep: the CW pass through j and right(j)
  - ccwNeighborStep, ccwProcStep: the backtrack at right(j) then j
  - right(j) is binary (it's on the outside arc, which includes binary procs)

  Then `BAFArcAdj.elim_of_binary_right` (BAFWord.lean:296) gives False.

  **Therefore:** each canonical gap is monotone (no backtracking). Both
  same-start monotone gaps have the same sign → global same-direction →
  finish assembly. -/

/-- **Canonical gap backtracking produces a BAFArcAdj entry conflict.**

    For a canonical (1,1) gap of a pivot t with binary neighbors,
    if the outside-arc walk backtracks at some processor j, then
    there exists a BAFArcAdj at j with right(j) binary, giving False
    via `BAFArcAdj.elim_of_binary_right`.

    This is the core new structural lemma for the lower bound proof.

    **Status**: sorry — requires:
    1. Extracting the first backtrack point j from the mover word.
    2. Building the BAFArcAdj witness (4 ordered steps + no-fire conditions)
       from the canonical gap structure and the backtrack.
    3. Proving right(j) is binary (from the outside-arc placement). -/
theorem canonical_gap_backtrack_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (_hbL : sys.rs.m (left t) = 2) (_hbR : sys.rs.m (right t) = 2)
    (_hfull : ∀ p : Fin sys.rs.n, 0 < gc.fireCount p)
    (_hn : sys.rs.n ≥ 9)
    -- Canonical gap data: phase with (J,K) = (1,1)
    (phase : TernaryPhase gc t)
    (_hJ1 : gc.intervalFireCount (left t) phase.a.val phase.s.val = 1)
    (_hK1 : gc.intervalFireCount (right t) phase.a.val phase.s.val = 1)
    -- The gap backtracks: some processor fires CW then the mover reverses
    (j : Fin sys.rs.n)
    (hj_ne_t : j ≠ t) (hj_ne_lt : j ≠ left t) (hj_ne_rt : j ≠ right t)
    -- Backtrack witness: j fires, then right(j) fires, then right(j) fires
    -- again (CCW), then j fires again (CCW) — creating the BAFArcAdj pattern
    (cwProcStep cwNeighborStep ccwNeighborStep ccwProcStep : Fin gc.configs.length)
    (hord1 : cwProcStep.val < cwNeighborStep.val)
    (hord2 : cwNeighborStep.val < ccwNeighborStep.val)
    (hord3 : ccwNeighborStep.val < ccwProcStep.val)
    (hcw_proc : gc.moverAt cwProcStep = j)
    (hcw_neighbor : gc.moverAt cwNeighborStep = right j)
    (hccw_neighbor : gc.moverAt ccwNeighborStep = right j)
    (hccw_proc : gc.moverAt ccwProcStep = j)
    (hadj : ccwProcStep.val = ccwNeighborStep.val + 1)
    -- No-fire conditions in the backtrack region
    (hj_nofire : ∀ k : Fin gc.configs.length,
      cwNeighborStep.val ≤ k.val → k.val < ccwProcStep.val → gc.moverAt k ≠ j)
    (hlj_nofire : ∀ k : Fin gc.configs.length,
      cwNeighborStep.val ≤ k.val → k.val < ccwProcStep.val → gc.moverAt k ≠ left j)
    (hrj_nofire_mid : ∀ k : Fin gc.configs.length,
      cwNeighborStep.val < k.val → k.val < ccwNeighborStep.val → gc.moverAt k ≠ right j)
    -- right(j) is binary (from position on the outside arc with ≥3 binary)
    (hbin_rj : isBinary sys.rs (right j)) :
    hasEntryConflict gc := by
  -- Construct the BAFArcAdj witness from the given data.
  let arc : BAFArcAdj gc := {
    proc := j
    cwProcStep := cwProcStep
    cwNeighborStep := cwNeighborStep
    ccwNeighborStep := ccwNeighborStep
    ccwProcStep := ccwProcStep
    cw_order := hord1
    mid_order := hord2
    ccw_order := hord3
    cw_proc_mover := hcw_proc
    cw_neighbor_mover := hcw_neighbor
    ccw_neighbor_mover := hccw_neighbor
    ccw_proc_mover := hccw_proc
    proc_noFire := hj_nofire
    leftProc_noFire := hlj_nofire
    rightProc_noFire_mid := hrj_nofire_mid
    ccw_adjacent := hadj
  }
  -- BAFArcAdj with binary right(j) → False → hasEntryConflict
  exfalso
  exact arc.elim_of_binary_right hbin_rj

/-! ### Step 6b: Gap uniform direction + same-start → global uniform -/

/-- A canonical gap has uniform direction `d`: every non-t step in the gap
    has `gc.stepDir k = d`, where `d` is `.cw` or `.ccw` (not `.stay`). -/
def GapUniformDir {sys : System} {gc : GoodCycle sys} {t : Fin sys.rs.n}
    (phase : TernaryPhase gc t) (d : StepDir) : Prop :=
  (d = .cw ∨ d = .ccw) ∧
  ∀ k : Fin gc.configs.length,
    phase.a.val ≤ k.val → k.val < phase.s.val →
    gc.stepDir k = d

/-- **Same-start uniform-direction canonical gaps force global uniform direction.**

    When both canonical (1,1) gaps of a pivot t have the same uniform
    direction `d` (every step in each gap goes the same way), and the
    two t-fires also advance in direction `d` (from same-start), the
    entire cycle is unidirectional.

    **Proof sketch:**
    1. `hfc_t = 2` means t fires at exactly two steps s₁, s₂.
    2. The two canonical gaps partition all non-t steps.
    3. Every non-t step has `stepDir = d` (from `hgap1`, `hgap2`).
    4. The t-steps also have `stepDir = d` (from `hsameStart`: the
       step after each t-fire launches toward the same neighbor,
       which determines the direction of the t-step itself).
    5. All steps have `stepDir = d` → `gc.uniformDirection`.

    **Status**: sorry — requires formalizing that the canonical gaps
    partition all steps and that hsameStart determines t-step direction. -/
theorem canonical_sameStart_monotone_gaps_uniform
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (_hbL : sys.rs.m (left t) = 2) (_hbR : sys.rs.m (right t) = 2)
    (_hfull : ∀ p : Fin sys.rs.n, 0 < gc.fireCount p)
    (_hn : sys.rs.n ≥ 9)
    (hfc_t : gc.fireCount t = 2)
    -- Two canonical phases covering all non-t steps
    (phase1 phase2 : TernaryPhase gc t)
    (hJ1 : gc.intervalFireCount (left t) phase1.a.val phase1.s.val = 1)
    (hK1 : gc.intervalFireCount (right t) phase1.a.val phase1.s.val = 1)
    (hJ2 : gc.intervalFireCount (left t) phase2.a.val phase2.s.val = 1)
    (hK2 : gc.intervalFireCount (right t) phase2.a.val phase2.s.val = 1)
    -- Both gaps have the same uniform direction d
    (d : StepDir)
    (hgap1 : GapUniformDir phase1 d)
    (hgap2 : GapUniformDir phase2 d)
    -- Same start: the first mover after each t-fire is the same neighbor,
    -- determining the direction of the t-step itself.
    -- Concretely: the step AT phase.s (= t-fire) has stepDir = d,
    -- because the next mover (= first mover of next gap) is in direction d from t.
    (ht_step1 : gc.stepDir phase1.s = d)
    (ht_step2 : gc.stepDir phase2.s = d)
    -- The two t-fires and two gaps cover all steps
    (hcover : ∀ k : Fin gc.configs.length,
      (phase1.a.val ≤ k.val ∧ k.val ≤ phase1.s.val) ∨
      (phase2.a.val ≤ k.val ∧ k.val ≤ phase2.s.val)) :
    gc.uniformDirection := by
  rcases hgap1 with ⟨hd, hgap1⟩
  rcases hgap2 with ⟨_, hgap2⟩
  rcases hd with hd | hd
  · refine Or.inl ?_
    intro k
    have hkdir : gc.stepDir k = .cw := by
      rcases hcover k with hk1 | hk2
      · by_cases hks : k.val = phase1.s.val
        · have hk_eq : k = phase1.s := Fin.ext hks
          simpa [hk_eq, hd] using ht_step1
        · have hlt : k.val < phase1.s.val := by omega
          simpa [hd] using hgap1 k hk1.1 hlt
      · by_cases hks : k.val = phase2.s.val
        · have hk_eq : k = phase2.s := Fin.ext hks
          simpa [hk_eq, hd] using ht_step2
        · have hlt : k.val < phase2.s.val := by omega
          simpa [hd] using hgap2 k hk2.1 hlt
    exact gc.eq_right_of_stepDir_eq_cw hkdir
  · refine Or.inr ?_
    intro k
    have hkdir : gc.stepDir k = .ccw := by
      rcases hcover k with hk1 | hk2
      · by_cases hks : k.val = phase1.s.val
        · have hk_eq : k = phase1.s := Fin.ext hks
          simpa [hk_eq, hd] using ht_step1
        · have hlt : k.val < phase1.s.val := by omega
          simpa [hd] using hgap1 k hk1.1 hlt
      · by_cases hks : k.val = phase2.s.val
        · have hk_eq : k = phase2.s := Fin.ext hks
          simpa [hk_eq, hd] using ht_step2
        · have hlt : k.val < phase2.s.val := by omega
          simpa [hd] using hgap2 k hk2.1 hlt
    exact gc.eq_left_of_stepDir_eq_ccw hkdir

/-! ### Convergence transfer under config-list rotation

    Two GoodCycles with the same config *set* have identical `badStep`
    relations, hence identical `converges` properties.  This lets us
    rotate gc's config list to align moverAt(0) with proc 0, build the
    WaterfallCycle on the rotated copy, apply the shadow theorem there,
    and transfer `¬converges` back to the original gc. -/

/-- `badStep` depends only on membership in `gc.configs`, so two
    GoodCycles with the same membership yield the same relation. -/
private theorem badStep_eq_of_mem_iff
    (gc₁ gc₂ : GoodCycle sys)
    (hmem : ∀ c : Config sys.rs, c ∈ gc₁.configs ↔ c ∈ gc₂.configs) :
    badStep sys gc₁ = badStep sys gc₂ := by
  funext c' c
  apply propext
  simp only [badStep]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨mt (hmem c).mpr h1, mt (hmem c').mpr h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨mt (hmem c).mp h1, mt (hmem c').mp h2, h3⟩

/-- Convergence is invariant under config-list reorderings that preserve
    the set of configurations. -/
private theorem converges_iff_of_mem_iff
    (gc₁ gc₂ : GoodCycle sys)
    (hmem : ∀ c : Config sys.rs, c ∈ gc₁.configs ↔ c ∈ gc₂.configs) :
    converges sys gc₁ ↔ converges sys gc₂ := by
  unfold converges
  rw [badStep_eq_of_mem_iff gc₁ gc₂ hmem]

/-- Rotate a good cycle's config list by `off` positions.

    **Properties (all mechanical, index arithmetic):**
    - The rotated list has the same length.
    - The rotated list has the same elements (as a set).
    - The rotated list forms a valid GoodCycle (distinct, unique_privileged,
      closed are all preserved under cyclic rotation).
    - moverAt on the rotated cycle satisfies
      `moverAt_rot(k) = moverAt((k + off) % L)`.

    **Status**: sorry — mechanical index arithmetic on List.rotate. -/
private theorem exists_rotated_goodCycle (gc : GoodCycle sys) (off : Nat) :
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
      · -- privileged sys (rotConfigs.get k) i
        rw [get_rot k]; exact hpriv
      · -- rotConfigs.get (nextIndex rotConfigs k) = move sys (rotConfigs.get k) i
        rw [get_rot k]
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
      · obtain ⟨u, hu_priv, hu_unique⟩ := gc.unique_privileged (gc.configs.get k) (List.get_mem _ _)
        have hju : j = u := hu_unique j hj_priv_at_k
        have hiu : i = u := hu_unique i hpriv
        exact hju.trans hiu.symm
  }
  refine ⟨gc', ?_, ?_, ?_⟩
  -- Property 1: same membership
  · intro c; exact List.mem_rotate
  -- Property 2: same length
  · exact hrot_len
  -- Property 3: shifted moverAt
  · intro k
    have hpriv := gc'.moverAt_privileged k
    change privileged sys (rotConfigs.get k) (gc'.moverAt k) at hpriv
    rw [get_rot k] at hpriv
    exact gc.moverAt_unique ⟨(k.val + off) % L, Nat.mod_lt _ hLpos⟩ (gc'.moverAt k) hpriv

/-- Given a uniform CW good cycle with length 2n, the rotated cycle
    (with moverAt(0) = proc 0) admits a WaterfallCycle structure.

    Under the rotation by off = (n - moverAt(0).val) % n:
    - moverAt_rot(0) = proc 0  (by construction of off)
    - moverAt_rot(k) = proc k%n  (uniform CW preserved)
    - Proc i fires at rotated steps i and i+n
    - Between fires: proc i holds highVal(i) = config_rot[i+1][i]
    - Outside fires: proc i holds 0
    - The waterfall indicator (j-i) mod 2n ∈ [1,n] matches exactly.

    **Status**: sorry — waterfall verification is index arithmetic. -/
private theorem waterfallCycle_of_rotated_uniformCW
    (gc : GoodCycle sys) (hCW : gc.uniformCW)
    (_hfc_all : ∀ p : Fin sys.rs.n, gc.fireCount p = 2)
    (hL : gc.configs.length = 2 * sys.rs.n)
    (_hn : sys.rs.n ≥ 5)
    (gc' : GoodCycle sys)
    (_hmem : ∀ c : Config sys.rs, c ∈ gc'.configs ↔ c ∈ gc.configs)
    (hL' : gc'.configs.length = gc.configs.length)
    (hmover : ∀ k : Fin gc'.configs.length,
      gc'.moverAt k = gc.moverAt ⟨(k.val + (sys.rs.n - (gc.moverAt ⟨0, by rw [hL]; omega⟩).val) % sys.rs.n) % gc.configs.length,
        Nat.mod_lt _ (by have := gc.nonempty; omega)⟩)
    -- Rest value = 0: every proc's value at config 0 is 0.
    -- This holds after value relabeling (permute each proc's state space
    -- so rest value maps to 0). The caller provides this after relabeling.
    (hlowVal_zero : ∀ (i : Fin sys.rs.n),
      ((gc'.configs.get ⟨0, by rw [hL']; rw [hL]; omega⟩) i).val = 0) :
    ∃ wc : WaterfallCycle sys, wc.toGoodCycle = gc' := by
  -- Key derived facts
  have hn_pos : 0 < sys.rs.n := by have := sys.rs.n_ge_4; omega
  have hL'2n : gc'.configs.length = 2 * sys.rs.n := by omega
  -- The rotated cycle's mover pattern: moverAt'(k) = proc (k % n)
  -- Proof: hmover gives gc'.moverAt k = gc.moverAt ⟨(k + off) % L, ...⟩.
  -- Under uniformCW, gc.moverAt advances CW by 1 each step (induction).
  -- The rotation offset off = (n - p₀) % n aligns p₀ + off ≡ 0 (mod n).
  -- Combining: (gc'.moverAt k).val = (p₀ + (k + off) % (2n)) % n = k % n.
  -- Each step is standard modular arithmetic.
  have hmover_mod : ∀ k : Fin gc'.configs.length,
      (gc'.moverAt k).val = k.val % sys.rs.n := by
    -- Abbreviations
    set n := sys.rs.n with hn_def
    set L := gc.configs.length with hL_def
    have hL2n : L = 2 * n := hL
    have hLpos : 0 < L := by omega
    set p₀ := (gc.moverAt ⟨0, by omega⟩).val with hp₀_def
    have hp₀_lt : p₀ < n := (gc.moverAt ⟨0, by omega⟩).isLt
    set off := (n - p₀) % n with hoff_def
    -- Step 1: Under uniformCW, gc.moverAt ⟨j, _⟩ has val (p₀ + j) % n.
    have mover_orig : ∀ (j : Nat) (hj : j < L),
        (gc.moverAt ⟨j, hj⟩).val = (p₀ + j) % n := by
      intro j
      induction j with
      | zero =>
        intro hj
        simp only [Nat.add_zero]
        -- Goal: (gc.moverAt ⟨0, hj⟩).val = p₀ % n
        -- p₀ = (gc.moverAt ⟨0, by omega⟩).val, and ⟨0, hj⟩ = ⟨0, by omega⟩
        have : (⟨0, hj⟩ : Fin L) = ⟨0, hLpos⟩ := rfl
        rw [hp₀_def, Nat.mod_eq_of_lt hp₀_lt]
      | succ j' ih =>
        intro hj
        have hj' : j' < L := by omega
        -- hCW at step j' gives: moverAt(nextIndex(j')) = right(moverAt(j'))
        have hcw_j := hCW ⟨j', hj'⟩
        -- nextIndex ⟨j', hj'⟩ = ⟨(j'+1) % L, _⟩
        have hnext_val : (nextIndex gc.configs ⟨j', hj'⟩).val = (j' + 1) % L := by
          simp [nextIndex, hL_def]
        -- Since j'+1 = j'.succ < L, (j'+1) % L = j'+1
        have hmod_eq : (j' + 1) % L = j' + 1 := Nat.mod_eq_of_lt hj
        -- So nextIndex ⟨j', hj'⟩ = ⟨j'+1, hj⟩
        have hnext_eq : nextIndex gc.configs ⟨j', hj'⟩ = ⟨j' + 1, hj⟩ := by
          ext; rw [hnext_val, hmod_eq]
        rw [hnext_eq] at hcw_j
        -- hcw_j : gc.moverAt ⟨j'+1, hj⟩ = right (gc.moverAt ⟨j', hj'⟩)
        have := congrArg Fin.val hcw_j
        simp only [right_val] at this
        -- this : (gc.moverAt ⟨j'+1, hj⟩).val = ((gc.moverAt ⟨j', hj'⟩).val + 1) % n
        rw [ih hj'] at this
        -- this : ... = ((p₀ + j') % n + 1) % n
        rw [this]
        -- Goal: ((p₀ + j') % n + 1) % n = (p₀ + (j' + 1)) % n
        rw [show p₀ + (j' + 1) = p₀ + j' + 1 by ring]
        -- (a % n + 1) % n = (a + 1) % n
        have hmod_step : ((p₀ + j') % n + 1) % n = (p₀ + j' + 1) % n := by
          have h1n : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
          conv_lhs => rw [← h1n]
          exact (Nat.add_mod (p₀ + j') 1 n).symm
        exact hmod_step
    -- Step 2: Combine hmover with mover_orig.
    intro k
    have hk := hmover k
    -- hk : gc'.moverAt k = gc.moverAt ⟨(k.val + off) % L, _⟩
    have := congrArg Fin.val hk
    -- this : (gc'.moverAt k).val = (gc.moverAt ⟨(k.val + off) % L, _⟩).val
    rw [this]
    rw [mover_orig ((k.val + off) % L) (Nat.mod_lt _ hLpos)]
    -- Goal: (p₀ + (k.val + off) % L) % n = k.val % n
    -- Key: (x % (2*n)) % n = x % n, since n ∣ 2*n
    have hmod_reduce : (k.val + off) % L % n = (k.val + off) % n := by
      rw [hL2n]
      exact Nat.mod_mod_of_dvd _ ⟨2, by ring⟩
    rw [Nat.add_mod p₀ ((k.val + off) % L) n, hmod_reduce, ← Nat.add_mod]
    -- Goal: (p₀ + (k.val + off)) % n = k.val % n
    -- Expand off = (n - p₀) % n and show p₀ + off ≡ 0 (mod n)
    suffices h : (p₀ + off) % n = 0 by
      rw [show p₀ + (k.val + off) = k.val + (p₀ + off) by ring]
      rw [Nat.add_mod, h, Nat.add_zero, Nat.mod_mod_of_dvd]
      exact ⟨1, by ring⟩
    -- p₀ + off = p₀ + (n - p₀) % n
    rw [hoff_def]
    by_cases hp₀_zero : p₀ = 0
    · simp [hp₀_zero]
    · have hp₀_pos : 0 < p₀ := Nat.pos_of_ne_zero hp₀_zero
      have hn_sub_lt : n - p₀ < n := by omega
      rw [Nat.mod_eq_of_lt hn_sub_lt]
      -- p₀ + (n - p₀) = n
      have : p₀ + (n - p₀) = n := by omega
      rw [this, Nat.mod_self]
  -- Define highVal: the value of proc i at config (i+1) % (2n) in gc'
  let highVal : (i : Fin sys.rs.n) → Fin (sys.rs.m i) := fun i =>
    (gc'.configs.get ⟨(i.val + 1) % (2 * sys.rs.n),
      by rw [hL'2n]; exact Nat.mod_lt _ (by omega)⟩) i
  -- Helper: proc i does NOT fire at step k when k % n ≠ i.val
  have not_mover_of_mod_ne : ∀ (k : Fin gc'.configs.length) (i : Fin sys.rs.n),
      k.val % sys.rs.n ≠ i.val → gc'.moverAt k ≠ i := by
    intro k i hmod_ne hmov
    have h := hmover_mod k
    rw [hmov] at h
    exact hmod_ne h.symm
  -- Helper: value constancy for consecutive steps where proc i doesn't fire.
  -- If moverAt(k) ≠ i, then config[k][i] = config[k+1][i].
  have step_preserve : ∀ (k : Fin gc'.configs.length) (i : Fin sys.rs.n),
      gc'.moverAt k ≠ i →
      ∀ (hk1 : k.val + 1 < gc'.configs.length),
      (gc'.configs.get k) i = (gc'.configs.get ⟨k.val + 1, hk1⟩) i := by
    intro k i hne hk1
    have hval_eq := gc'.state_eq_of_ne_moverAt k i hne.symm
    have hnext_eq : nextIndex gc'.configs k = ⟨k.val + 1, hk1⟩ := by
      ext; simp [nextIndex, Nat.mod_eq_of_lt hk1]
    rw [hnext_eq] at hval_eq; exact hval_eq.symm
  -- Helper: value constancy over a range [a, b] where proc i doesn't fire at a..b-1.
  have range_preserve : ∀ (i : Fin sys.rs.n) (a b : Nat)
      (ha : a < gc'.configs.length) (hb : b < gc'.configs.length),
      a ≤ b →
      (∀ k, a ≤ k → k < b → k % sys.rs.n ≠ i.val) →
      (gc'.configs.get ⟨a, ha⟩) i = (gc'.configs.get ⟨b, hb⟩) i := by
    intro i a b ha hb hab hno_fire
    induction hab with
    | refl => rfl
    | step hab' ih =>
      rename_i b'
      have hb'_lt : b' < gc'.configs.length := by omega
      have := ih hb'_lt (fun k hk1 hk2 => hno_fire k hk1 (by omega))
      have hne : gc'.moverAt ⟨b', hb'_lt⟩ ≠ i :=
        not_mover_of_mod_ne ⟨b', hb'_lt⟩ i (hno_fire b' (by omega) (by omega))
      rw [this, step_preserve ⟨b', hb'_lt⟩ i hne (by omega)]
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Modular arithmetic helper: k % n ≠ i when k ≥ i, k - i ≠ 0, and k - i ≠ n.
  -- (i.e., k - i is not a multiple of n in the range [0, 2n))
  -- ═══════════════════════════════════════════════════════════════════════════
  have mod_ne_of_diff_not_mult : ∀ (k : Nat) (i : Fin sys.rs.n),
      k ≥ i.val → k - i.val ≠ 0 → k - i.val ≠ sys.rs.n →
      k - i.val < 2 * sys.rs.n →
      k % sys.rs.n ≠ i.val := by
    intro k i hkge hne0 hne_n hlt2n heq
    -- From k % n = i and k ≥ i: k - i is a multiple of n.
    have hk_decomp := Nat.div_add_mod k sys.rs.n
    rw [heq] at hk_decomp
    have hmult : k - i.val = sys.rs.n * (k / sys.rs.n) := by omega
    -- k - i < 2n, so k/n ∈ {0, 1}. k-i = n*(k/n).
    -- k/n = 0 → k-i = 0, contradicts hne0.
    -- k/n = 1 → k-i = n, contradicts hne_n.
    -- k/n ≥ 2 → k-i ≥ 2n, contradicts hlt2n.
    rcases Nat.eq_or_lt_of_le (Nat.zero_le (k / sys.rs.n)) with hq0 | hq_pos
    · -- k/n = 0
      rw [← hq0, Nat.mul_zero] at hmult; exact hne0 hmult
    · rcases Nat.eq_or_lt_of_le hq_pos with hq1 | hq_ge2
      · -- k/n = 1
        rw [← hq1, Nat.mul_one] at hmult; exact hne_n hmult
      · -- k/n ≥ 2
        have : sys.rs.n * (k / sys.rs.n) ≥ 2 * sys.rs.n := by
          calc sys.rs.n * (k / sys.rs.n) ≥ sys.rs.n * 2 := Nat.mul_le_mul_left _ hq_ge2
            _ = 2 * sys.rs.n := by ring
        omega
  -- ═══════════════════════════════════════════════════════════════════════════
  -- HIGH PHASE: config[j][i] = highVal(i) when d = (j + 2n - i) % 2n ∈ [1, n].
  -- ═══════════════════════════════════════════════════════════════════════════
  have high_phase : ∀ (j : Fin gc'.configs.length) (i : Fin sys.rs.n),
      let d := (j.val + 2 * sys.rs.n - i.val) % (2 * sys.rs.n)
      1 ≤ d → d ≤ sys.rs.n →
      (gc'.configs.get j) i = highVal i := by
    intro j i d hd1 hdn
    have hi_lt : i.val < sys.rs.n := i.isLt
    have hj_lt : j.val < 2 * sys.rs.n := hL'2n ▸ j.isLt
    -- Key: d ∈ [1,n] and d = (j+2n-i) % 2n. Since i < n, j < 2n:
    -- j+2n-i ∈ [n+1, 4n-1]. Modulo 2n: either j-i (if j ≥ i) or j+2n-i (if j < i).
    -- In either case, d ∈ [1,n] and i+d ≤ n+n-1 = 2n-1 < 2n means j = i+d (mod 2n)
    -- and j = i+d literally (since i+d < 2n and j < 2n).
    -- Step 1: prove j = i + d
    have hid_lt : i.val + d < 2 * sys.rs.n := by omega
    have hj_eq : j.val = i.val + d := by
      -- d = (j + 2n - i) % 2n. We know j < 2n and i < n < 2n.
      -- j + 2n - i ≥ j + 2n - (n-1) = j + n + 1 ≥ n + 1 > 0.
      -- Case j ≥ i: j + 2n - i = (j - i) + 2n, so d = (j - i) (since j-i < 2n).
      --   Then j = i + d. Check: i + d = i + (j-i) = j. OK.
      -- Case j < i: j + 2n - i < 2n (since j < i ≤ n-1, so j+2n-i < 2n).
      --   Then d = j + 2n - i. And i + d = i + j + 2n - i = j + 2n ≥ 2n.
      --   But i + d ≤ i + n ≤ 2n - 1. So j + 2n ≤ 2n - 1 → j ≤ -1. Contradiction.
      -- Therefore j ≥ i and d = j - i.
      by_cases hjge : j.val ≥ i.val
      · -- j ≥ i: d = (j + 2n - i) % 2n = (j - i + 2n) % 2n = (j - i) % 2n
        have hji_lt : j.val - i.val < 2 * sys.rs.n := by omega
        have hd_eq : d = j.val - i.val := by
          show (j.val + 2 * sys.rs.n - i.val) % (2 * sys.rs.n) = j.val - i.val
          have h1 : j.val + 2 * sys.rs.n - i.val = (j.val - i.val) + 1 * (2 * sys.rs.n) := by omega
          rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hji_lt]
        omega
      · -- j < i: impossible when d ∈ [1, n]
        push_neg at hjge
        -- j + 2n - i < 2n (since j < i ≤ n-1, so j+2n-i ≤ n-2+2n-0 = 3n-2... no)
        -- Actually j < i < n, so j ≤ n-2, and j + 2n - i ≥ 0 + 2n - (n-1) = n+1.
        -- And j + 2n - i ≤ (n-2) + 2n - 0 = 3n - 2.
        -- So d = (j+2n-i) % 2n. If j+2n-i < 2n: d = j+2n-i ≥ n+1 > n. Contradicts hdn.
        -- If j+2n-i ≥ 2n: d = j+2n-i-2n = j-i, but j < i so j-i = 0 in Nat. d = 0 < 1.
        --   Contradicts hd1. Unless we need to be careful: j + 2n - i ≥ 2n iff j ≥ i.
        --   Since j < i: j + 2n - i < 2n. So d = j + 2n - i ≥ n + 1 > n.
        exfalso
        have : j.val + 2 * sys.rs.n - i.val < 2 * sys.rs.n := by omega
        have hd_eq : d = j.val + 2 * sys.rs.n - i.val := by
          show (j.val + 2 * sys.rs.n - i.val) % (2 * sys.rs.n) = _
          exact Nat.mod_eq_of_lt this
        omega
    -- Step 2: highVal(i) = config[(i+1) % 2n][i]. Since i+1 < 2n: (i+1) % 2n = i+1.
    have hi1_mod : (i.val + 1) % (2 * sys.rs.n) = i.val + 1 :=
      Nat.mod_eq_of_lt (by omega)
    -- Step 3: range_preserve from i+1 to j (= i+d) where d ∈ [1,n].
    -- For k ∈ [i+1, j-1] = [i+1, i+d-1], k - i ∈ [1, d-1] ⊆ [1, n-1].
    -- mod_ne_of_diff_pos gives k % n ≠ i.
    rw [show j = ⟨i.val + d, by rw [hL'2n]; omega⟩ from Fin.ext hj_eq]
    show (gc'.configs.get ⟨i.val + d, _⟩) i =
      (gc'.configs.get ⟨(i.val + 1) % (2 * sys.rs.n), _⟩) i
    rw [show (⟨(i.val + 1) % (2 * sys.rs.n), _⟩ : Fin gc'.configs.length) =
      ⟨i.val + 1, by rw [hL'2n]; omega⟩ from Fin.ext hi1_mod]
    exact (range_preserve i (i.val + 1) (i.val + d)
      (by rw [hL'2n]; omega) (by rw [hL'2n]; omega) (by omega)
      (fun k hk1 hk2 => mod_ne_of_diff_not_mult k i (by omega) (by omega) (by omega) (by omega))).symm
  -- ═══════════════════════════════════════════════════════════════════════════
  -- LOW PHASE: config[j][i] = config[0][i] when d ∉ [1, n].
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Wrap-around constancy: moverAt(2n-1) = proc (n-1), so for i ≠ n-1:
  -- config[0][i] = config[2n-1][i].
  have wrap_preserve : ∀ (i : Fin sys.rs.n),
      i.val ≠ sys.rs.n - 1 →
      (gc'.configs.get ⟨0, by omega⟩) i =
      (gc'.configs.get ⟨2 * sys.rs.n - 1, by rw [hL'2n]; omega⟩) i := by
    intro i hi_ne
    have h2n1_lt : 2 * sys.rs.n - 1 < gc'.configs.length := by rw [hL'2n]; omega
    have hne : gc'.moverAt ⟨2 * sys.rs.n - 1, h2n1_lt⟩ ≠ i := by
      apply not_mover_of_mod_ne
      -- (2n-1) % n = n - 1
      show (2 * sys.rs.n - 1) % sys.rs.n ≠ i.val
      rw [show 2 * sys.rs.n - 1 = (sys.rs.n - 1) + 1 * sys.rs.n from by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : sys.rs.n - 1 < sys.rs.n)]
      exact hi_ne.symm
    have hval_eq := gc'.state_eq_of_ne_moverAt ⟨2 * sys.rs.n - 1, h2n1_lt⟩ i hne.symm
    have hnext_eq : nextIndex gc'.configs ⟨2 * sys.rs.n - 1, h2n1_lt⟩ = ⟨0, by omega⟩ := by
      ext; simp [nextIndex, hL'2n]
      show (2 * sys.rs.n - 1 + 1) % (2 * sys.rs.n) = 0
      have : 2 * sys.rs.n - 1 + 1 = 2 * sys.rs.n := by omega
      rw [this, Nat.mod_self]
    rw [hnext_eq] at hval_eq; exact hval_eq
  have low_phase : ∀ (j : Fin gc'.configs.length) (i : Fin sys.rs.n),
      let d := (j.val + 2 * sys.rs.n - i.val) % (2 * sys.rs.n)
      ¬(1 ≤ d ∧ d ≤ sys.rs.n) →
      (gc'.configs.get j) i = (gc'.configs.get ⟨0, by omega⟩) i := by
    intro j i d hd
    push_neg at hd
    have hi_lt : i.val < sys.rs.n := i.isLt
    have hj_lt : j.val < 2 * sys.rs.n := hL'2n ▸ j.isLt
    -- Case analysis: j ≤ i or j > i
    by_cases hjle : j.val ≤ i.val
    · -- Case A: j ≤ i (before first fire at step i)
      -- k ∈ [0, j-1], k < i < n, so k%n = k ≠ i.
      exact (range_preserve i 0 j.val (by omega) j.isLt (by omega) (fun k hk1 hk2 => by
        have : k < i.val := by omega
        have : k < sys.rs.n := by omega
        rw [Nat.mod_eq_of_lt (by omega : k < sys.rs.n)]
        omega)).symm
    · push_neg at hjle
      -- j > i. Compute d = j - i (since j > i ≥ 0 and j < 2n).
      have hjge : j.val ≥ i.val := by omega
      have hji_lt : j.val - i.val < 2 * sys.rs.n := by omega
      have hd_eq : d = j.val - i.val := by
        show (j.val + 2 * sys.rs.n - i.val) % (2 * sys.rs.n) = j.val - i.val
        have h1 : j.val + 2 * sys.rs.n - i.val = (j.val - i.val) + 1 * (2 * sys.rs.n) := by omega
        rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hji_lt]
      -- d ∉ [1, n] and d = j - i ≥ 1 means d > n, i.e., j ≥ i + n + 1.
      have hd_pos : d ≥ 1 := by omega
      have hd_gt_n : d > sys.rs.n := by
        rcases hd hd_pos with hd_gt; exact hd_gt
      have hj_ge_in1 : j.val ≥ i.val + sys.rs.n + 1 := by omega
      -- i = n-1 is impossible: j ≥ n-1+n+1 = 2n, but j < 2n.
      by_cases hi_last : i.val = sys.rs.n - 1
      · exfalso; omega
      · -- i ≤ n-2. Chain: config[j] → config[i+n+1] → config[2n-1] → config[0].
        have hi_le : i.val ≤ sys.rs.n - 2 := by omega
        -- Step 1: config[j][i] = config[i+n+1][i] via range_preserve.
        -- For k ∈ [i+n+1, j-1]: k-i ∈ [n+1, j-i-1]. j-i ≤ 2n-1 so k-i ≤ 2n-2.
        -- k-i ≠ 0 (since k ≥ i+n+1 > i), k-i ≠ n (since k ≥ i+n+1 means k-i ≥ n+1 > n).
        have hin1_lt : i.val + sys.rs.n + 1 < gc'.configs.length := by rw [hL'2n]; omega
        have h1 : (gc'.configs.get j) i =
            (gc'.configs.get ⟨i.val + sys.rs.n + 1, hin1_lt⟩) i := by
          exact (range_preserve i (i.val + sys.rs.n + 1) j.val hin1_lt j.isLt
            (by omega)
            (fun k hk1 hk2 => mod_ne_of_diff_not_mult k i
              (by omega) (by omega) (by omega) (by omega))).symm
        -- Step 2: config[i+n+1][i] = config[2n-1][i] via range_preserve.
        -- For k ∈ [i+n+1, 2n-2]: same argument (k-i ∈ [n+1, 2n-2-i], none = 0 or n).
        have h2n1_lt : 2 * sys.rs.n - 1 < gc'.configs.length := by rw [hL'2n]; omega
        have h2 : (gc'.configs.get ⟨i.val + sys.rs.n + 1, hin1_lt⟩) i =
            (gc'.configs.get ⟨2 * sys.rs.n - 1, h2n1_lt⟩) i := by
          exact range_preserve i (i.val + sys.rs.n + 1) (2 * sys.rs.n - 1) hin1_lt h2n1_lt
            (by omega)
            (fun k hk1 hk2 => mod_ne_of_diff_not_mult k i
              (by omega) (by omega) (by omega) (by omega))
        -- Step 3: config[2n-1][i] = config[0][i] via wrap_preserve.
        have h3 := (wrap_preserve i (by omega)).symm
        -- Chain all three.
        rw [h1, h2, h3]
  -- ═══════════════════════════════════════════════════════════════════════════
  -- lowVal = 0 for all processors (from hypothesis hlowVal_zero).
  have lowVal_zero : ∀ (i : Fin sys.rs.n),
      ((gc'.configs.get ⟨0, by omega⟩) i).val = 0 := hlowVal_zero
  -- highVal is nonzero: state_ne_at_moverAt at step i says
  -- config[i+1][i] ≠ config[i][i], i.e., highVal(i) ≠ lowVal(i) = 0.
  have highVal_pos : ∀ i, (highVal i).val ≠ 0 := by
    intro i
    have hi_lt : i.val < sys.rs.n := i.isLt
    have hi_step : i.val < gc'.configs.length := by rw [hL'2n]; omega
    -- moverAt(i) = proc i (from hmover_mod)
    have hmov_i : gc'.moverAt ⟨i.val, hi_step⟩ = i := by
      ext; rw [hmover_mod]; exact Nat.mod_eq_of_lt hi_lt
    -- state_ne_at_moverAt: config[nextIndex(i)][i] ≠ config[i][i]
    have hne := gc'.state_ne_at_moverAt ⟨i.val, hi_step⟩
    rw [hmov_i] at hne
    -- nextIndex(i) = i+1
    have hi1_lt : i.val + 1 < gc'.configs.length := by rw [hL'2n]; omega
    have hnext_eq : nextIndex gc'.configs ⟨i.val, hi_step⟩ = ⟨i.val + 1, hi1_lt⟩ := by
      ext; simp [nextIndex, Nat.mod_eq_of_lt hi1_lt]
    rw [hnext_eq] at hne
    -- config[i][i] = config[0][i] (low phase before first fire)
    have hlow : (gc'.configs.get ⟨i.val, hi_step⟩) i =
        (gc'.configs.get ⟨0, by omega⟩) i := by
      exact (range_preserve i 0 i.val (by omega) hi_step (by omega) (fun k hk1 hk2 => by
        -- k ∈ [0, i-1], so 1 ≤ i - k ≤ i ≤ n-1. By mod_ne_of_diff_pos (reversed): k%n ≠ i.
        -- Actually: k < i < n, so k % n = k (since k < n), and k ≠ i.
        have hk_lt_i : k < i.val := by omega
        have hk_lt_n : k < sys.rs.n := by omega
        rw [Nat.mod_eq_of_lt hk_lt_n]
        omega)).symm
    have hval0 : ((gc'.configs.get ⟨i.val, hi_step⟩) i).val = 0 := by
      rw [hlow]; exact lowVal_zero i
    -- highVal(i) = config[(i+1) % 2n][i] = config[i+1][i]
    show (highVal i).val ≠ 0
    change ((gc'.configs.get ⟨(i.val + 1) % (2 * sys.rs.n), _⟩) i).val ≠ 0
    have hi1_mod : (i.val + 1) % (2 * sys.rs.n) = i.val + 1 :=
      Nat.mod_eq_of_lt (by omega)
    rw [show (⟨(i.val + 1) % (2 * sys.rs.n), _⟩ : Fin gc'.configs.length) =
      ⟨i.val + 1, hi1_lt⟩ from Fin.ext hi1_mod]
    -- If config[i+1][i].val = 0, then config[i+1][i] = config[i][i], contradicting hne.
    intro heq0
    have : ((gc'.configs.get ⟨i.val + 1, hi1_lt⟩) i).val =
        ((gc'.configs.get ⟨i.val, hi_step⟩) i).val := by
      rw [heq0, hval0]
    exact hne (Fin.ext this)
  -- ═══════════════════════════════════════════════════════════════════════════
  -- WATERFALL: combine high_phase and low_phase with lowVal_zero.
  -- ═══════════════════════════════════════════════════════════════════════════
  have waterfall : ∀ (j : Fin gc'.configs.length) (i : Fin sys.rs.n),
      let d := (j.val + 2 * sys.rs.n - i.val) % (2 * sys.rs.n)
      if 1 ≤ d ∧ d ≤ sys.rs.n
      then (gc'.configs.get j) i = highVal i
      else (gc'.configs.get j) i = ⟨0, by have := sys.rs.m_pos i; omega⟩ := by
    intro j i
    simp only
    split
    · -- HIGH phase
      rename_i hd
      exact high_phase j i hd.1 hd.2
    · -- LOW phase
      rename_i hd
      have hlow := low_phase j i hd
      rw [hlow]
      ext; exact lowVal_zero i
  -- Assemble the WaterfallCycle and prove toGoodCycle = gc'
  exact ⟨{
    toGoodCycle := gc'
    len_eq := hL'2n
    highVal := highVal
    highVal_pos := highVal_pos
    waterfall := waterfall
  }, rfl⟩

/-! ### Value relabeling infrastructure

For each processor i, define a permutation σ_i on Fin(m_i) that swaps
restVal(i) with 0. Conjugating the system's transition function by these
per-processor permutations yields an isomorphic system where the rest
value is 0. The relabeled good cycle has lowVal = 0 by construction,
so WaterfallCycle can be built directly. -/

/-- Swap permutation: swaps values `a` and `b`, fixes everything else. -/
def swapPerm {n : Nat} (a b : Fin n) : Fin n → Fin n := fun x =>
  if x = a then b
  else if x = b then a
  else x

theorem swapPerm_involutive {n : Nat} (a b : Fin n) :
    ∀ x, swapPerm a b (swapPerm a b x) = x := by
  intro x
  simp only [swapPerm]
  split <;> split <;> simp_all <;> split <;> simp_all

theorem swapPerm_a {n : Nat} (a b : Fin n) :
    swapPerm a b a = b := by simp [swapPerm]

/-- Relabel a configuration by applying per-processor permutations. -/
def relabelConfig (rs : RingSpec)
    (σ : (i : Fin rs.n) → Fin (rs.m i) → Fin (rs.m i))
    (c : Config rs) : Config rs :=
  fun i => σ i (c i)

/-- Relabel a system by conjugating its transition function.
    sys_r.rs = sys.rs (same ring spec). -/
def relabelSystem (sys : System)
    (σ : (i : Fin sys.rs.n) → Fin (sys.rs.m i) → Fin (sys.rs.m i))
    (σ_inv : (i : Fin sys.rs.n) → Fin (sys.rs.m i) → Fin (sys.rs.m i)) : System where
  rs := sys.rs
  f := fun i L S R =>
    σ i (sys.f i (σ_inv (left i) L) (σ_inv i S) (σ_inv (right i) R))

@[simp] private theorem relabelSystem_rs (sys : System)
    (σ σ_inv : (i : Fin sys.rs.n) → Fin (sys.rs.m i) → Fin (sys.rs.m i)) :
    (relabelSystem sys σ σ_inv).rs = sys.rs := rfl

/-- List.get on a mapped list gives the function applied to the original element.
    This avoids dependent-type rewriting issues with List.get and List.map. -/
private theorem list_get_map {α β : Type} (l : List α) (f : α → β) (i : Nat)
    (hi : i < l.length) (hi2 : i < (l.map f).length) :
    (l.map f).get ⟨i, hi2⟩ = f (l.get ⟨i, hi⟩) := by
  induction l generalizing i with
  | nil => exact absurd hi (by simp)
  | cons a rest ih =>
    match i with
    | 0 => rfl
    | i + 1 =>
      show (rest.map f).get ⟨i, by simpa using hi2⟩ = f (rest.get ⟨i, by simpa using hi⟩)
      exact ih i (by simpa using hi) (by simpa using hi2)

/-- Variant: if l₁ = l₂.map f then l₁.get ⟨i, _⟩ = f (l₂.get ⟨i, _⟩). -/
private theorem list_get_of_eq_map {α β : Type} {l₁ : List β} {l₂ : List α} {f : α → β}
    (heq : l₁ = l₂.map f) (i : Nat) (hi₁ : i < l₁.length) (hi₂ : i < l₂.length) :
    l₁.get ⟨i, hi₁⟩ = f (l₂.get ⟨i, hi₂⟩) := by
  subst heq
  exact list_get_map l₂ f i hi₂ hi₁

/-- Convergence transfers through value relabeling.

    **Proof sketch**: The relabeling σ is a bijection on configs.
    A bad chain c₀ →_bad c₁ →_bad ... in sys_r maps (via σ⁻¹)
    to a bad chain in sys. WellFoundedness transfers.

    **Status**: sorry — mechanical well-foundedness transfer via
    order isomorphism. The key facts are:
    - step sys c c' ↔ step sys_r (σ c) (σ c')  [conjugation]
    - c ∈ gc.configs ↔ σ c ∈ gc_r.configs  [hmem_iff] -/
private theorem converges_relabel
    (sys : System)
    (σ : (i : Fin sys.rs.n) → Fin (sys.rs.m i) → Fin (sys.rs.m i))
    (σ_inv : (i : Fin sys.rs.n) → Fin (sys.rs.m i) → Fin (sys.rs.m i))
    (_h_inv : ∀ i x, σ_inv i (σ i x) = x)
    (_h_inv2 : ∀ i x, σ i (σ_inv i x) = x)
    (gc : GoodCycle sys)
    (gc_r : GoodCycle (relabelSystem sys σ σ_inv))
    (_hmem_iff : ∀ c : Config sys.rs,
      c ∈ gc.configs ↔ relabelConfig sys.rs σ c ∈ gc_r.configs) :
    converges sys gc → converges (relabelSystem sys σ σ_inv) gc_r := by
  intro hconv
  unfold converges at *
  -- Map badStep of sys_r back to badStep of sys via σ_inv
  let σ_inv_config : Config sys.rs → Config sys.rs := relabelConfig sys.rs σ_inv
  -- Show the relation maps
  have hbad_map : ∀ a b : Config sys.rs,
      badStep (relabelSystem sys σ σ_inv) gc_r a b →
      badStep sys gc (σ_inv_config a) (σ_inv_config b) := by
    intro a b ⟨hb_not_mem, ha_not_mem, hstep⟩
    -- Helper: relabelConfig σ ∘ relabelConfig σ_inv = id
    have σ_σ_inv_id : ∀ c : Config sys.rs,
        relabelConfig sys.rs σ (relabelConfig sys.rs σ_inv c) = c := by
      intro c; funext j; simp [relabelConfig, _h_inv2]
    refine ⟨?_, ?_, ?_⟩
    · -- σ_inv b ∉ gc.configs
      intro hmem
      apply hb_not_mem
      have := (_hmem_iff (σ_inv_config b)).mp hmem
      rwa [σ_σ_inv_id b] at this
    · -- σ_inv a ∉ gc.configs
      intro hmem
      apply ha_not_mem
      have := (_hmem_iff (σ_inv_config a)).mp hmem
      rwa [σ_σ_inv_id a] at this
    · -- step sys (σ_inv b) (σ_inv a)
      obtain ⟨i, hpriv, ha_eq⟩ := hstep
      use i
      constructor
      · simp only [privileged, relabelSystem, relabelConfig, σ_inv_config] at hpriv ⊢
        intro heq
        apply hpriv
        have := congrArg (σ i) heq
        simp only [_h_inv2] at this
        exact this
      · funext j
        simp only [move, σ_inv_config, relabelConfig]
        by_cases hji : j = i
        · subst hji
          have ha_j : a j = (relabelSystem sys σ σ_inv).f j (b (left j)) (b j) (b (right j)) := by
            have := congrFun ha_eq j
            simp [move] at this
            exact this
          rw [ha_j]
          simp [relabelSystem, _h_inv]
        · have ha_j : a j = b j := by
            have := congrFun ha_eq j
            simp [move, hji] at this
            exact this
          rw [ha_j]
          simp [hji]
  -- Transfer well-foundedness via σ_inv_config
  -- Use InvImage: badStep sys_r gc_r is contained in InvImage (badStep sys gc) σ_inv_config
  exact WellFounded.intro (fun d => by
    -- Build Acc for d by induction on Acc for σ_inv_config d
    suffices ∀ (x : Config sys.rs) (d : Config sys.rs),
        x = σ_inv_config d → Acc (badStep sys gc) x → Acc (badStep (relabelSystem sys σ σ_inv) gc_r) d from
      this _ d rfl (hconv.apply _)
    intro x d hxd hacc
    induction hacc generalizing d with
    | intro x _ ih =>
      exact Acc.intro d (fun a hbad => by
        have hbad' := hbad_map a d hbad
        rw [← hxd] at hbad'
        exact ih (σ_inv_config a) hbad' a rfl))

/-- Existence of a relabeled GoodCycle with the expected config list.

    Given a GoodCycle gc of sys, the config list `gc.configs.map (relabelConfig σ)`
    forms a GoodCycle of `relabelSystem sys σ σ_inv`.

    **Status**: sorry — mechanical: privileged/closed/distinct all transfer
    through the per-proc bijection σ. -/
private theorem relabeled_goodCycle_exists
    (sys : System)
    (σ : (i : Fin sys.rs.n) → Fin (sys.rs.m i) → Fin (sys.rs.m i))
    (σ_inv : (i : Fin sys.rs.n) → Fin (sys.rs.m i) → Fin (sys.rs.m i))
    (_h_inv : ∀ i x, σ_inv i (σ i x) = x)
    (_h_inv2 : ∀ i x, σ i (σ_inv i x) = x)
    (gc : GoodCycle sys) :
    ∃ gc_r : GoodCycle (relabelSystem sys σ σ_inv),
      gc_r.configs = gc.configs.map (relabelConfig sys.rs σ) ∧
      (∀ c : Config sys.rs, c ∈ gc.configs ↔
        relabelConfig sys.rs σ c ∈ gc_r.configs) := by
  -- Build the relabeled GoodCycle explicitly
  let configs_r := gc.configs.map (relabelConfig sys.rs σ)
  -- Nonempty
  have hne : configs_r ≠ [] := by simp [configs_r, gc.nonempty]
  -- Helper: relabelConfig σ is injective (since σ is pointwise bijective)
  have σ_inj : ∀ c₁ c₂ : Config sys.rs,
      relabelConfig sys.rs σ c₁ = relabelConfig sys.rs σ c₂ → c₁ = c₂ := by
    intro c₁ c₂ heq
    funext j
    have := congrFun heq j
    simp only [relabelConfig] at this
    -- σ j (c₁ j) = σ j (c₂ j), and σ j is injective (has left inverse σ_inv j)
    have h1 := congrArg (σ_inv j) this
    simp only [_h_inv] at h1
    exact h1
  -- Helper: σ ∘ σ_inv = id pointwise
  have σ_σ_inv_id : ∀ c : Config sys.rs,
      relabelConfig sys.rs σ (relabelConfig sys.rs σ_inv c) = c := by
    intro c; funext j; simp [relabelConfig, _h_inv2]
  -- Helper: σ_inv ∘ σ = id pointwise
  have σ_inv_σ_id : ∀ c : Config sys.rs,
      relabelConfig sys.rs σ_inv (relabelConfig sys.rs σ c) = c := by
    intro c; funext j; simp [relabelConfig, _h_inv]
  -- Helper: privileged equivalence
  have hpriv_iff : ∀ (c : Config sys.rs) (p : Fin sys.rs.n),
      privileged sys c p ↔ privileged (relabelSystem sys σ σ_inv) (relabelConfig sys.rs σ c) p := by
    intro c p
    simp only [privileged, relabelSystem, relabelConfig]
    constructor
    · intro h habs
      apply h
      have := congrArg (σ_inv p) habs
      simp only [_h_inv] at this
      exact this
    · intro h habs
      apply h
      show σ p (sys.f p (σ_inv (left p) (σ (left p) (c (left p))))
        (σ_inv p (σ p (c p))) (σ_inv (right p) (σ (right p) (c (right p))))) = σ p (c p)
      simp only [_h_inv]
      exact congrArg (σ p) habs
  -- Helper: move commutes with relabeling
  have move_relabel : ∀ (c : Config sys.rs) (i : Fin sys.rs.n),
      relabelConfig sys.rs σ (move sys c i) = move (relabelSystem sys σ σ_inv) (relabelConfig sys.rs σ c) i := by
    intro c i
    funext j
    simp only [move, relabelConfig, relabelSystem]
    by_cases hji : j = i
    · subst hji; simp [_h_inv]
    · simp [hji]
  -- Helper: list length
  have hlen : configs_r.length = gc.configs.length := by simp [configs_r]
  -- Helper: nextIndex on mapped list
  have hnext_map : ∀ k : Fin configs_r.length,
      (nextIndex configs_r k).val = (nextIndex gc.configs ⟨k.val, by have := k.isLt; omega⟩).val := by
    intro k; simp [nextIndex, hlen]
  -- unique_privileged
  have huniq : ∀ c ∈ configs_r, ∃! i, privileged (relabelSystem sys σ σ_inv) c i := by
    intro c hc
    rw [List.mem_map] at hc
    obtain ⟨c₀, hc₀_mem, hc₀_eq⟩ := hc
    subst hc₀_eq
    obtain ⟨i, hi, huniq⟩ := gc.unique_privileged c₀ hc₀_mem
    exact ⟨i, (hpriv_iff c₀ i).mp hi, fun j hj => huniq j ((hpriv_iff c₀ j).mpr hj)⟩
  -- closed
  have hclosed : ∀ k : Fin configs_r.length,
      ∃ i, privileged (relabelSystem sys σ σ_inv) (configs_r.get k) i ∧
        configs_r.get (nextIndex configs_r k) =
          move (relabelSystem sys σ σ_inv) (configs_r.get k) i := by
    intro k
    have hk : k.val < gc.configs.length := by have := k.isLt; omega
    -- configs_r.get k = relabelConfig sys.rs σ (gc.configs.get ⟨k.val, hk⟩)
    have hget_k := list_get_map gc.configs (relabelConfig sys.rs σ) k.val hk k.isLt
    -- configs_r.get (nextIndex configs_r k) = relabelConfig sys.rs σ (gc.configs.get (nextIndex gc.configs ⟨k.val, hk⟩))
    have hnk := nextIndex configs_r k
    have hnk_val := hnext_map k
    have hget_nk := list_get_map gc.configs (relabelConfig sys.rs σ)
      (nextIndex gc.configs ⟨k.val, hk⟩).val
      (nextIndex gc.configs ⟨k.val, hk⟩).isLt
      (Nat.lt_of_lt_of_eq (nextIndex gc.configs ⟨k.val, hk⟩).isLt hlen.symm)
    have hnk_lt_r : (nextIndex gc.configs ⟨k.val, hk⟩).val < configs_r.length :=
      Nat.lt_of_lt_of_eq (nextIndex gc.configs ⟨k.val, hk⟩).isLt hlen.symm
    have hnk_eq : (nextIndex configs_r k) = ⟨(nextIndex gc.configs ⟨k.val, hk⟩).val,
        hnk_lt_r⟩ := by
      ext; exact hnk_val
    -- From gc.closed
    obtain ⟨i, hpriv_i, hstep_i⟩ := gc.closed ⟨k.val, hk⟩
    use i
    constructor
    · -- privileged in relabeled system
      rw [hget_k]
      exact (hpriv_iff (gc.configs.get ⟨k.val, hk⟩) i).mp hpriv_i
    · -- step matches
      conv_lhs => rw [hnk_eq]
      rw [hget_nk, hstep_i, move_relabel, hget_k]
  -- distinct
  have hdist : ∀ j₁ j₂ : Fin configs_r.length,
      configs_r.get j₁ = configs_r.get j₂ → j₁ = j₂ := by
    intro j₁ j₂ heq
    have hj₁ : j₁.val < gc.configs.length := by have := j₁.isLt; omega
    have hj₂ : j₂.val < gc.configs.length := by have := j₂.isLt; omega
    have h₁ := list_get_map gc.configs (relabelConfig sys.rs σ) j₁.val hj₁ j₁.isLt
    have h₂ := list_get_map gc.configs (relabelConfig sys.rs σ) j₂.val hj₂ j₂.isLt
    rw [h₁, h₂] at heq
    have := σ_inj _ _ heq
    have hfin := gc.distinct ⟨j₁.val, hj₁⟩ ⟨j₂.val, hj₂⟩ this
    have := Fin.ext_iff.mp hfin
    exact Fin.ext this
  have hfair : ∀ i : Fin sys.rs.n,
      ∃ k : Fin configs_r.length,
        ∃ j, privileged (relabelSystem sys σ σ_inv) (configs_r.get k) j ∧
          configs_r.get (nextIndex configs_r k) =
            move (relabelSystem sys σ σ_inv) (configs_r.get k) j ∧ j = i := by
    intro i
    obtain ⟨k, j0, hpriv, hstep, hj0⟩ := gc.fair i
    subst j0
    have hk : k.val < gc.configs.length := k.isLt
    have hk_r : k.val < configs_r.length := by simpa [hlen] using hk
    let k_r : Fin configs_r.length := ⟨k.val, hk_r⟩
    have hget_k : configs_r.get k_r = relabelConfig sys.rs σ (gc.configs.get k) := by
      exact list_get_map gc.configs (relabelConfig sys.rs σ) k.val hk hk_r
    have hnext_val : (nextIndex configs_r k_r).val = (nextIndex gc.configs k).val := by
      simpa [k_r] using hnext_map k_r
    have hnext_lt_r : (nextIndex gc.configs k).val < configs_r.length := by
      exact Nat.lt_of_lt_of_eq (nextIndex gc.configs k).isLt hlen.symm
    have hnext_eq : nextIndex configs_r k_r =
        ⟨(nextIndex gc.configs k).val, hnext_lt_r⟩ := by
      ext
      exact hnext_val
    have hget_next : configs_r.get (nextIndex configs_r k_r) =
        relabelConfig sys.rs σ (gc.configs.get (nextIndex gc.configs k)) := by
      rw [hnext_eq]
      exact list_get_map gc.configs (relabelConfig sys.rs σ)
        (nextIndex gc.configs k).val (nextIndex gc.configs k).isLt hnext_lt_r
    refine ⟨k_r, i, ?_, ?_, rfl⟩
    · rw [hget_k]
      exact (hpriv_iff (gc.configs.get k) i).mp hpriv
    · rw [hget_next, hstep, move_relabel, hget_k]
  -- Build the GoodCycle
  let gc_r : GoodCycle (relabelSystem sys σ σ_inv) :=
    ⟨configs_r, hne, huniq, hclosed, hdist, hfair⟩
  refine ⟨gc_r, rfl, fun c => ⟨fun hc => ?_, fun hc => ?_⟩⟩
  · -- c ∈ gc.configs → relabelConfig sys.rs σ c ∈ gc_r.configs
    show relabelConfig sys.rs σ c ∈ configs_r
    simp [configs_r, List.mem_map]
    exact ⟨c, hc, rfl⟩
  · -- relabelConfig sys.rs σ c ∈ gc_r.configs → c ∈ gc.configs
    show c ∈ gc.configs
    have : relabelConfig sys.rs σ c ∈ configs_r := hc
    simp [configs_r, List.mem_map] at this
    obtain ⟨c₀, hc₀_mem, hc₀_eq⟩ := this
    have := σ_inj c c₀ hc₀_eq.symm
    rw [this]
    exact hc₀_mem

/-- A WaterfallCycle can be built from a relabeled uniform CW good cycle
    whose lowVal is 0 by construction.

    **Status**: sorry — the waterfall form transfers through relabeling.
    The high/low phase structure depends only on the mover pattern
    (preserved by relabeling) and the fact that lowVal = 0. -/
private theorem waterfallCycle_of_relabeled
    {sys_r : System}
    (gc_r : GoodCycle sys_r)
    (_hL : gc_r.configs.length = 2 * sys_r.rs.n)
    (_hn : sys_r.rs.n ≥ 5)
    (_hlowVal : ∀ (i : Fin sys_r.rs.n),
      ((gc_r.configs.get ⟨0, by omega⟩) i).val = 0)
    -- The mover pattern is proc (k % n) (uniform CW after rotation)
    (_hmover_mod : ∀ k : Fin gc_r.configs.length,
      (gc_r.moverAt k).val = k.val % sys_r.rs.n) :
    ∃ wc : WaterfallCycle sys_r, wc.toGoodCycle = gc_r := by
  -- Define highVal: the value of proc i at config (i+1) % (2n)
  -- This is the value after proc i fires for the first time
  set n := sys_r.rs.n with hn_def
  have hn_pos : 0 < n := by omega
  have hL_pos : 0 < gc_r.configs.length := by omega
  let highVal : (i : Fin n) → Fin (sys_r.rs.m i) := fun i =>
    (gc_r.configs.get ⟨(i.val + 1) % (2 * n),
      by rw [_hL]; exact Nat.mod_lt _ (by omega)⟩) i
  -- Helper: proc i does NOT fire at step k when k % n ≠ i.val
  have not_mover_of_mod_ne_r : ∀ (k : Fin gc_r.configs.length) (i : Fin n),
      k.val % n ≠ i.val → gc_r.moverAt k ≠ i := by
    intro k i hmod_ne hmov
    have h1 := _hmover_mod k
    rw [hmov] at h1
    exact hmod_ne h1.symm
  -- Helper: value constancy for consecutive steps where proc i doesn't fire
  have step_preserve_r : ∀ (k : Fin gc_r.configs.length) (i : Fin n),
      gc_r.moverAt k ≠ i →
      ∀ (hk1 : k.val + 1 < gc_r.configs.length),
      (gc_r.configs.get k) i = (gc_r.configs.get ⟨k.val + 1, hk1⟩) i := by
    intro k i hne hk1
    have hval_eq := gc_r.state_eq_of_ne_moverAt k i hne.symm
    have hnext_eq : nextIndex gc_r.configs k = ⟨k.val + 1, hk1⟩ := by
      ext; simp [nextIndex, Nat.mod_eq_of_lt hk1]
    rw [hnext_eq] at hval_eq; exact hval_eq.symm
  -- Helper: value constancy over a range [a, b) where proc i doesn't fire
  have range_preserve_r : ∀ (i : Fin n) (a b : Nat)
      (ha : a < gc_r.configs.length) (hb : b < gc_r.configs.length),
      a ≤ b →
      (∀ k, a ≤ k → k < b → k % n ≠ i.val) →
      (gc_r.configs.get ⟨a, ha⟩) i = (gc_r.configs.get ⟨b, hb⟩) i := by
    intro i a b ha hb hab hno_fire
    induction hab with
    | refl => rfl
    | step hab' ih =>
      rename_i b'
      have hb'_lt : b' < gc_r.configs.length := by omega
      have := ih hb'_lt (fun k hk1 hk2 => hno_fire k hk1 (by omega))
      have hne : gc_r.moverAt ⟨b', hb'_lt⟩ ≠ i :=
        not_mover_of_mod_ne_r ⟨b', hb'_lt⟩ i (hno_fire b' (by omega) (by omega))
      rw [this, step_preserve_r ⟨b', hb'_lt⟩ i hne (by omega)]
  -- HIGH phase: config[j][i] = highVal(i) when d ∈ [1,n]
  -- Proof: proc i fires at step i (from hmover_mod), changing to highVal.
  -- Between steps i+1 and j, proc i doesn't fire. range_preserve gives constancy.
  -- Modular arithmetic helper: k % n ≠ i when k ≥ i, k - i ≠ 0, k - i ≠ n, k - i < 2n.
  have mod_ne_of_diff_not_mult_r : ∀ (k : Nat) (i : Fin n),
      k ≥ i.val → k - i.val ≠ 0 → k - i.val ≠ n →
      k - i.val < 2 * n →
      k % n ≠ i.val := by
    intro k i hkge hne0 hne_n hlt2n heq
    have hk_decomp := Nat.div_add_mod k n
    rw [heq] at hk_decomp
    have hmult : k - i.val = n * (k / n) := by omega
    rcases Nat.eq_or_lt_of_le (Nat.zero_le (k / n)) with hq0 | hq_pos
    · rw [← hq0, Nat.mul_zero] at hmult; exact hne0 hmult
    · rcases Nat.eq_or_lt_of_le hq_pos with hq1 | hq_ge2
      · rw [← hq1, Nat.mul_one] at hmult; exact hne_n hmult
      · have : n * (k / n) ≥ 2 * n := by
          calc n * (k / n) ≥ n * 2 := Nat.mul_le_mul_left _ hq_ge2
            _ = 2 * n := by ring
        omega
  have high_phase_r : ∀ (j : Fin gc_r.configs.length) (i : Fin n),
      let d := (j.val + 2 * n - i.val) % (2 * n)
      1 ≤ d → d ≤ n →
      (gc_r.configs.get j) i = highVal i := by
    intro j i d hd1 hdn
    have hi_lt : i.val < n := i.isLt
    have hj_lt : j.val < 2 * n := _hL ▸ j.isLt
    -- Step 1: prove j = i + d
    have hid_lt : i.val + d < 2 * n := by omega
    have hj_eq : j.val = i.val + d := by
      by_cases hjge : j.val ≥ i.val
      · have hji_lt : j.val - i.val < 2 * n := by omega
        have hd_eq : d = j.val - i.val := by
          show (j.val + 2 * n - i.val) % (2 * n) = j.val - i.val
          have h1 : j.val + 2 * n - i.val = (j.val - i.val) + 1 * (2 * n) := by omega
          rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hji_lt]
        omega
      · push_neg at hjge
        exfalso
        have : j.val + 2 * n - i.val < 2 * n := by omega
        have hd_eq : d = j.val + 2 * n - i.val := by
          show (j.val + 2 * n - i.val) % (2 * n) = _
          exact Nat.mod_eq_of_lt this
        omega
    -- Step 2: highVal(i) = config[(i+1) % 2n][i]. Since i+1 < 2n: (i+1) % 2n = i+1.
    have hi1_mod : (i.val + 1) % (2 * n) = i.val + 1 :=
      Nat.mod_eq_of_lt (by omega)
    -- Step 3: range_preserve from i+1 to j (= i+d).
    rw [show j = ⟨i.val + d, by rw [_hL]; omega⟩ from Fin.ext hj_eq]
    show (gc_r.configs.get ⟨i.val + d, _⟩) i =
      (gc_r.configs.get ⟨(i.val + 1) % (2 * n), _⟩) i
    rw [show (⟨(i.val + 1) % (2 * n), _⟩ : Fin gc_r.configs.length) =
      ⟨i.val + 1, by rw [_hL]; omega⟩ from Fin.ext hi1_mod]
    exact (range_preserve_r i (i.val + 1) (i.val + d)
      (by rw [_hL]; omega) (by rw [_hL]; omega) (by omega)
      (fun k hk1 hk2 => mod_ne_of_diff_not_mult_r k i (by omega) (by omega) (by omega) (by omega))).symm
  -- LOW phase: config[j][i] = config[0][i] when d ∉ [1,n]
  -- Proof: proc i doesn't fire between steps i+n+1 and i (wrapping through 0).
  -- range_preserve + wrap_around gives constancy back to config[0][i].
  -- Wrap-around constancy: moverAt(2n-1) = proc (n-1), so for i ≠ n-1:
  -- config[0][i] = config[2n-1][i].
  have wrap_preserve_r : ∀ (i : Fin n),
      i.val ≠ n - 1 →
      (gc_r.configs.get ⟨0, by omega⟩) i =
      (gc_r.configs.get ⟨2 * n - 1, by rw [_hL]; omega⟩) i := by
    intro i hi_ne
    have h2n1_lt : 2 * n - 1 < gc_r.configs.length := by rw [_hL]; omega
    have hne : gc_r.moverAt ⟨2 * n - 1, h2n1_lt⟩ ≠ i := by
      apply not_mover_of_mod_ne_r
      show (2 * n - 1) % n ≠ i.val
      rw [show 2 * n - 1 = (n - 1) + 1 * n from by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
      exact hi_ne.symm
    have hval_eq := gc_r.state_eq_of_ne_moverAt ⟨2 * n - 1, h2n1_lt⟩ i hne.symm
    have hnext_eq : nextIndex gc_r.configs ⟨2 * n - 1, h2n1_lt⟩ = ⟨0, by omega⟩ := by
      ext; simp [nextIndex, _hL]
      show (2 * n - 1 + 1) % (2 * n) = 0
      have : 2 * n - 1 + 1 = 2 * n := by omega
      rw [this, Nat.mod_self]
    rw [hnext_eq] at hval_eq; exact hval_eq
  have low_phase_r : ∀ (j : Fin gc_r.configs.length) (i : Fin n),
      let d := (j.val + 2 * n - i.val) % (2 * n)
      ¬(1 ≤ d ∧ d ≤ n) →
      (gc_r.configs.get j) i = (gc_r.configs.get ⟨0, by omega⟩) i := by
    intro j i d hd
    push_neg at hd
    have hi_lt : i.val < n := i.isLt
    have hj_lt : j.val < 2 * n := _hL ▸ j.isLt
    by_cases hjle : j.val ≤ i.val
    · -- Case A: j ≤ i (before first fire at step i)
      exact (range_preserve_r i 0 j.val (by omega) j.isLt (by omega) (fun k hk1 hk2 => by
        have : k < i.val := by omega
        have : k < n := by omega
        rw [Nat.mod_eq_of_lt (by omega : k < n)]
        omega)).symm
    · push_neg at hjle
      -- j > i. Compute d = j - i.
      have hjge : j.val ≥ i.val := by omega
      have hji_lt : j.val - i.val < 2 * n := by omega
      have hd_eq : d = j.val - i.val := by
        show (j.val + 2 * n - i.val) % (2 * n) = j.val - i.val
        have h1 : j.val + 2 * n - i.val = (j.val - i.val) + 1 * (2 * n) := by omega
        rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hji_lt]
      -- d ∉ [1, n] and d = j - i ≥ 1 means d > n.
      have hd_pos : d ≥ 1 := by omega
      have hd_gt_n : d > n := by
        rcases hd hd_pos with hd_gt; exact hd_gt
      have hj_ge_in1 : j.val ≥ i.val + n + 1 := by omega
      -- i = n-1 is impossible: j ≥ n-1+n+1 = 2n, but j < 2n.
      by_cases hi_last : i.val = n - 1
      · exfalso; omega
      · -- i ≤ n-2. Chain: config[j] → config[i+n+1] → config[2n-1] → config[0].
        have hi_le : i.val ≤ n - 2 := by omega
        -- Step 1: config[j][i] = config[i+n+1][i]
        have hin1_lt : i.val + n + 1 < gc_r.configs.length := by rw [_hL]; omega
        have h1 : (gc_r.configs.get j) i =
            (gc_r.configs.get ⟨i.val + n + 1, hin1_lt⟩) i := by
          exact (range_preserve_r i (i.val + n + 1) j.val hin1_lt j.isLt
            (by omega)
            (fun k hk1 hk2 => mod_ne_of_diff_not_mult_r k i
              (by omega) (by omega) (by omega) (by omega))).symm
        -- Step 2: config[i+n+1][i] = config[2n-1][i]
        have h2n1_lt : 2 * n - 1 < gc_r.configs.length := by rw [_hL]; omega
        have h2 : (gc_r.configs.get ⟨i.val + n + 1, hin1_lt⟩) i =
            (gc_r.configs.get ⟨2 * n - 1, h2n1_lt⟩) i := by
          exact range_preserve_r i (i.val + n + 1) (2 * n - 1) hin1_lt h2n1_lt
            (by omega)
            (fun k hk1 hk2 => mod_ne_of_diff_not_mult_r k i
              (by omega) (by omega) (by omega) (by omega))
        -- Step 3: config[2n-1][i] = config[0][i]
        have h3 := (wrap_preserve_r i (by omega)).symm
        rw [h1, h2, h3]
  -- lowVal = 0 (from hypothesis)
  have lowVal_zero_r := _hlowVal
  -- highVal_pos and waterfall: same structure as waterfallCycle_of_rotated_uniformCW
  -- but adapted for sys_r/gc_r. Uses range_preserve_r + lowVal_zero_r + hmover_mod.
  -- The proofs are identical in structure to the ones proved for the original system
  -- in waterfallCycle_of_rotated_uniformCW (lines 2053-2330), just with sys_r variables.
  -- highVal_pos and waterfall for the relabeled system.
  -- These are structurally identical to the proofs in waterfallCycle_of_rotated_uniformCW
  -- for the original system. The proofs use range_preserve_r, not_mover_of_mod_ne_r,
  -- step_preserve_r, and lowVal_zero_r — all proved above.
  -- The only remaining work is Fin/index arithmetic to connect the high_phase
  -- and low_phase constancy arguments. This is ~40 lines per proof, purely mechanical.
  have highVal_pos_r : ∀ i, (highVal i).val ≠ 0 := by
    intro i
    have hi_lt : i.val < n := i.isLt
    have hi_step : i.val < gc_r.configs.length := by rw [_hL]; omega
    -- moverAt(i) = proc i (from _hmover_mod)
    have hmov_i : gc_r.moverAt ⟨i.val, hi_step⟩ = i := by
      ext; rw [_hmover_mod]; exact Nat.mod_eq_of_lt hi_lt
    -- state_ne_at_moverAt: config[nextIndex(i)][i] ≠ config[i][i]
    have hne := gc_r.state_ne_at_moverAt ⟨i.val, hi_step⟩
    rw [hmov_i] at hne
    -- nextIndex(i) = i+1
    have hi1_lt : i.val + 1 < gc_r.configs.length := by rw [_hL]; omega
    have hnext_eq : nextIndex gc_r.configs ⟨i.val, hi_step⟩ = ⟨i.val + 1, hi1_lt⟩ := by
      ext; simp [nextIndex, Nat.mod_eq_of_lt hi1_lt]
    rw [hnext_eq] at hne
    -- config[i][i] = config[0][i] (low phase before first fire)
    have hlow : (gc_r.configs.get ⟨i.val, hi_step⟩) i =
        (gc_r.configs.get ⟨0, by omega⟩) i := by
      exact (range_preserve_r i 0 i.val (by omega) hi_step (by omega) (fun k hk1 hk2 => by
        have hk_lt_i : k < i.val := by omega
        have hk_lt_n : k < n := by omega
        rw [Nat.mod_eq_of_lt (by omega : k < n)]
        omega)).symm
    have hval0 : ((gc_r.configs.get ⟨i.val, hi_step⟩) i).val = 0 := by
      rw [hlow]; exact lowVal_zero_r i
    -- highVal(i) = config[(i+1) % 2n][i] = config[i+1][i]
    show (highVal i).val ≠ 0
    change ((gc_r.configs.get ⟨(i.val + 1) % (2 * n), _⟩) i).val ≠ 0
    have hi1_mod : (i.val + 1) % (2 * n) = i.val + 1 :=
      Nat.mod_eq_of_lt (by omega)
    rw [show (⟨(i.val + 1) % (2 * n), _⟩ : Fin gc_r.configs.length) =
      ⟨i.val + 1, hi1_lt⟩ from Fin.ext hi1_mod]
    intro heq0
    have : ((gc_r.configs.get ⟨i.val + 1, hi1_lt⟩) i).val =
        ((gc_r.configs.get ⟨i.val, hi_step⟩) i).val := by
      rw [heq0, hval0]
    exact hne (Fin.ext this)
  have waterfall_r : ∀ (j : Fin gc_r.configs.length) (i : Fin n),
      let d := (j.val + 2 * n - i.val) % (2 * n)
      if 1 ≤ d ∧ d ≤ n
      then (gc_r.configs.get j) i = highVal i
      else (gc_r.configs.get j) i = ⟨0, by have := sys_r.rs.m_pos i; omega⟩ := by
    intro j i
    simp only
    split
    · -- HIGH phase
      rename_i hd
      exact high_phase_r j i hd.1 hd.2
    · -- LOW phase
      rename_i hd
      have hlow := low_phase_r j i hd
      rw [hlow]
      ext; exact lowVal_zero_r i
  exact ⟨{
    toGoodCycle := gc_r
    len_eq := _hL
    highVal := highVal
    highVal_pos := highVal_pos_r
    waterfall := waterfall_r
  }, rfl⟩

/-- A uniform CW good cycle with length 2n and all fire counts = 2
    cannot be the good cycle of a convergent system.

    **Proof**: Rotate config list so moverAt(0) = proc 0, define value
    relabeling so lowVal = 0, build WaterfallCycle on the relabeled copy,
    apply shadow_cycle_mirror_theorem, then transfer ¬converges back.

    The relabeling approach avoids proving lowVal = 0 for the original
    system (which is false for ternary procs). Instead, we:
    1. Rotate gc → gc' with moverAt(0) = proc 0
    2. Define σ_i = swap(restVal_i, 0) for each proc i
    3. Build relabeled system sys_r and GoodCycle gc_r with lowVal = 0
    4. Build WaterfallCycle from gc_r (lowVal = 0 by construction)
    5. Apply shadow_cycle_mirror_theorem → ¬converges sys_r gc_r
    6. Transfer: converges sys gc → converges sys_r gc_r (isomorphism)
    7. Contrapositive → ¬converges sys gc -/
private theorem uniformCW_not_converges
    (gc : GoodCycle sys) (hCW : gc.uniformCW)
    (hfc_all : ∀ p : Fin sys.rs.n, gc.fireCount p = 2)
    (hL : gc.configs.length = 2 * sys.rs.n)
    (hn : sys.rs.n ≥ 5)
    (h3bin : hasGe3Binary sys.rs) :
    ¬converges sys gc := by
  -- Step 1: Rotate gc so moverAt(0) = proc 0.
  let off := (sys.rs.n - (gc.moverAt ⟨0, by rw [hL]; omega⟩).val) % sys.rs.n
  obtain ⟨gc', hmem', hlen', hmover'⟩ := exists_rotated_goodCycle gc off
  -- Step 2: Define value relabeling.
  let c0 : Config sys.rs := gc'.configs.get ⟨0, by rw [hlen']; rw [hL]; omega⟩
  let σ : (i : Fin sys.rs.n) → Fin (sys.rs.m i) → Fin (sys.rs.m i) :=
    fun i => swapPerm (c0 i) ⟨0, by have := sys.rs.m_pos i; omega⟩
  -- σ is its own inverse (swapPerm is an involution)
  let σ_inv := σ
  have h_inv : ∀ i x, σ_inv i (σ i x) = x :=
    fun i x => swapPerm_involutive (c0 i) ⟨0, by have := sys.rs.m_pos i; omega⟩ x
  have h_inv2 : ∀ i x, σ i (σ_inv i x) = x := h_inv
  -- Step 3: Build relabeled system and GoodCycle.
  let sys_r := relabelSystem sys σ σ_inv
  obtain ⟨gc_r, hgc_r_configs, hgc_r_mem⟩ :=
    relabeled_goodCycle_exists sys σ σ_inv h_inv h_inv2 gc'
  -- Step 4: lowVal = 0 by construction.
  have hgc_r_len : gc_r.configs.length = gc'.configs.length := by
    rw [hgc_r_configs, List.length_map]
  have hgc_r_pos : 0 < gc_r.configs.length := by rw [hgc_r_len, hlen', hL]; omega
  have hlowVal_r : ∀ (i : Fin sys_r.rs.n),
      ((gc_r.configs.get ⟨0, hgc_r_pos⟩) i).val = 0 := by
    intro i
    -- gc_r.configs = gc'.configs.map (relabelConfig sys.rs σ)
    -- gc_r.configs[0] = σ applied to gc'.configs[0] = c0
    -- σ i (c0 i) = swapPerm (c0 i) 0 (c0 i) = 0
    -- The 0th element of gc_r.configs is in gc_r.configs
    -- and it's the relabeling of c0
    -- Use gc_r.distinct + membership to identify the config
    -- Actually, use that gc_r.configs is gc'.configs.map σ, so
    -- the head of gc_r.configs is σ applied to the head of gc'.configs
    -- Work with the list directly via nth_map
    have hlen_pos : 0 < gc'.configs.length := by rw [hlen']; rw [hL]; omega
    -- Direct: unfold the 0th config
    -- gc_r.configs.get ⟨0, _⟩ ∈ gc_r.configs
    -- relabelConfig sys.rs σ c0 ∈ gc_r.configs (from hgc_r_mem)
    -- These could be different elements. We need the list structure.
    -- Since gc_r.configs = L.map f, gc_r.configs.get ⟨0, _⟩ = f (L.get ⟨0, _⟩) = f c0
    -- Let's use List.get_eq_iff or work by cases on the list
    -- Actually let's just match on gc'.configs
    -- We need: (gc_r.configs.get ⟨0, hgc_r_pos⟩ i).val = 0
    -- gc_r.configs = gc'.configs.map (relabelConfig sys.rs σ), so the 0th element
    -- is (relabelConfig sys.rs σ) applied to the 0th element of gc'.configs = c0
    -- (relabelConfig sys.rs σ c0) i = σ i (c0 i) = swapPerm (c0 i) 0 (c0 i) = 0
    --
    -- Prove via List.head: if l.head = x then l.get ⟨0, _⟩ = x
    -- gc_r.configs.head = relabelConfig sys.rs σ (gc'.configs.head)
    have hne_r : gc_r.configs ≠ [] := gc_r.nonempty
    have hne' : gc'.configs ≠ [] := gc'.nonempty
    -- List.get ⟨0, _⟩ = List.head for nonempty lists
    have get_zero_eq_head {α : Type} (l : List α) (hne : l ≠ []) (h : 0 < l.length) :
        l.get ⟨0, h⟩ = l.head hne := by
      match l, hne with
      | a :: _, _ => rfl
    have head_map {α β : Type} (l : List α) (f : α → β) (hne : l ≠ [])
        (hne2 : l.map f ≠ []) :
        (l.map f).head hne2 = f (l.head hne) := by
      match l, hne with
      | a :: _, _ => rfl
    have hne_mapped : (gc'.configs.map (relabelConfig sys.rs σ)) ≠ [] := by
      simp [hne']
    rw [get_zero_eq_head gc_r.configs hne_r hgc_r_pos]
    -- gc_r.configs.head = (gc'.configs.map (relabelConfig sys.rs σ)).head
    have hhead : gc_r.configs.head hne_r =
        (gc'.configs.map (relabelConfig sys.rs σ)).head hne_mapped := by
      congr 1
    rw [hhead, head_map gc'.configs (relabelConfig sys.rs σ) hne' hne_mapped]
    simp only [relabelConfig]
    -- goal: (σ i (gc'.configs.head hne' i)).val = 0
    -- gc'.configs.head hne' = gc'.configs.get ⟨0, _⟩ = c0
    rw [← get_zero_eq_head gc'.configs hne' hlen_pos]
    change (swapPerm (c0 i) ⟨0, _⟩ (c0 i)).val = 0
    rw [swapPerm_a]
  -- Step 5: The relabeled cycle has the right mover pattern.
  -- sys_r.rs = sys.rs, so sys_r.rs.n = sys.rs.n.
  have hrs_eq : sys_r.rs = sys.rs := rfl
  have hn_r_eq : sys_r.rs.n = sys.rs.n := rfl
  have hL_r : gc_r.configs.length = 2 * sys_r.rs.n := by
    rw [hn_r_eq, hgc_r_configs, List.length_map, hlen', hL]
  -- The mover pattern of gc_r matches gc' (relabeling preserves movers).
  have hmover_mod_r : ∀ k : Fin gc_r.configs.length,
      (gc_r.moverAt k).val = k.val % sys_r.rs.n := by
    intro k
    -- Step A: relabeling preserves privileged status, so gc_r.moverAt k = gc'.moverAt k'
    -- Step B: gc' inherits uniformCW from gc, with moverAt(0) = proc 0
    -- Step C: uniformCW + moverAt(0) = 0 implies moverAt(k) = k % n
    -- For now, combine these facts:
    have hk' : k.val < gc'.configs.length := by
      have := k.isLt; omega
    -- The relabeling preserves which proc is privileged at each step
    -- because privileged sys c p ↔ privileged sys_r (σ c) p
    -- (σ is per-proc bijection, sys_r.f conjugates by σ)
    have hpriv_iff : ∀ (c : Config sys.rs) (p : Fin sys.rs.n),
        privileged sys c p ↔ privileged (relabelSystem sys σ σ_inv) (relabelConfig sys.rs σ c) p := by
      intro c p
      simp only [privileged, relabelSystem, relabelConfig]
      constructor
      · intro h habs
        apply h
        have := congrArg (σ_inv p) habs
        simp only [h_inv] at this
        exact this
      · intro h habs
        apply h
        show σ p (sys.f p (σ_inv (left p) (σ (left p) (c (left p))))
          (σ_inv p (σ p (c p))) (σ_inv (right p) (σ (right p) (c (right p))))) = σ p (c p)
        simp only [h_inv]
        exact congrArg (σ p) habs
    -- Show gc_r.moverAt k = gc'.moverAt ⟨k.val, hk'⟩ via uniqueness
    -- First: gc_r.configs.get k = relabelConfig sys.rs σ (gc'.configs.get ⟨k.val, hk'⟩)
    -- from hgc_r_configs: gc_r.configs = gc'.configs.map (relabelConfig sys.rs σ)
    have hget_eq : gc_r.configs.get k =
        relabelConfig sys.rs σ (gc'.configs.get ⟨k.val, hk'⟩) := by
      exact list_get_of_eq_map hgc_r_configs k.val k.isLt hk'
    -- gc'.moverAt ⟨k.val, hk'⟩ is privileged in gc_r at step k
    have hpriv_at_k : privileged (relabelSystem sys σ σ_inv) (gc_r.configs.get k)
        (gc'.moverAt ⟨k.val, hk'⟩) := by
      have hpriv_gc' := gc'.moverAt_privileged ⟨k.val, hk'⟩
      rw [hpriv_iff (gc'.configs.get ⟨k.val, hk'⟩) (gc'.moverAt ⟨k.val, hk'⟩)] at hpriv_gc'
      rw [hget_eq]
      exact hpriv_gc'
    -- By moverAt_unique
    have hmover_eq : gc'.moverAt ⟨k.val, hk'⟩ = gc_r.moverAt k :=
      gc_r.moverAt_unique k _ hpriv_at_k
    -- Now relate gc'.moverAt to k % n using uniformCW + rotation
    rw [← hmover_eq]
    -- Reuse the mover pattern proof from waterfallCycle_of_rotated_uniformCW
    set n' := sys.rs.n with hn_def
    set L := gc.configs.length with hL_def
    have hL2n : L = 2 * n' := hL
    have hLpos : 0 < L := by omega
    set p₀ := (gc.moverAt ⟨0, by omega⟩).val with hp₀_def
    have hp₀_lt : p₀ < n' := (gc.moverAt ⟨0, by omega⟩).isLt
    -- Step 1: Under uniformCW, gc.moverAt ⟨j, _⟩ has val (p₀ + j) % n
    have mover_orig : ∀ (j : Nat) (hj : j < L),
        (gc.moverAt ⟨j, hj⟩).val = (p₀ + j) % n' := by
      intro j
      induction j with
      | zero =>
        intro hj
        simp only [Nat.add_zero]
        have : (⟨0, hj⟩ : Fin L) = ⟨0, hLpos⟩ := rfl
        rw [hp₀_def, Nat.mod_eq_of_lt hp₀_lt]
      | succ j' ih =>
        intro hj
        have hj' : j' < L := by omega
        have hcw_j := hCW ⟨j', hj'⟩
        have hnext_val : (nextIndex gc.configs ⟨j', hj'⟩).val = (j' + 1) % L := by
          simp [nextIndex, hL_def]
        have hmod_eq : (j' + 1) % L = j' + 1 := Nat.mod_eq_of_lt hj
        have hnext_eq : nextIndex gc.configs ⟨j', hj'⟩ = ⟨j' + 1, hj⟩ := by
          ext; rw [hnext_val, hmod_eq]
        rw [hnext_eq] at hcw_j
        have := congrArg Fin.val hcw_j
        simp only [right_val] at this
        rw [ih hj'] at this
        rw [this]
        rw [show p₀ + (j' + 1) = p₀ + j' + 1 by ring]
        have hmod_step : ((p₀ + j') % n' + 1) % n' = (p₀ + j' + 1) % n' := by
          have h1n : 1 % n' = 1 := Nat.mod_eq_of_lt (by omega)
          conv_lhs => rw [← h1n]
          exact (Nat.add_mod (p₀ + j') 1 n').symm
        exact hmod_step
    -- Step 2: Combine hmover' with mover_orig
    have hk_hmover := hmover' ⟨k.val, hk'⟩
    have := congrArg Fin.val hk_hmover
    rw [this]
    rw [mover_orig ((k.val + off) % L) (Nat.mod_lt _ hLpos)]
    -- Goal: (p₀ + (k.val + off) % L) % n' = k.val % n'
    -- Note: sys_r.rs.n = sys.rs.n = n' (by rfl)
    have hmod_reduce : (k.val + off) % L % n' = (k.val + off) % n' := by
      rw [hL2n]
      exact Nat.mod_mod_of_dvd _ ⟨2, by ring⟩
    rw [Nat.add_mod p₀ ((k.val + off) % L) n', hmod_reduce, ← Nat.add_mod]
    suffices h : (p₀ + off) % n' = 0 by
      rw [show p₀ + (k.val + off) = k.val + (p₀ + off) by ring]
      rw [Nat.add_mod, h, Nat.add_zero, Nat.mod_mod_of_dvd _ ⟨1, by ring⟩]
      rfl
    -- p₀ + off = p₀ + (n' - p₀) % n'
    -- off = (n' - p₀) % n' (by definition, since n' = sys.rs.n)
    have hoff_eq : off = (n' - p₀) % n' := by rfl
    rw [hoff_eq]
    by_cases hp₀_zero : p₀ = 0
    · simp [hp₀_zero]
    · have hp₀_pos : 0 < p₀ := Nat.pos_of_ne_zero hp₀_zero
      have hn_sub_lt : n' - p₀ < n' := by omega
      rw [Nat.mod_eq_of_lt hn_sub_lt]
      have : p₀ + (n' - p₀) = n' := by omega
      rw [this, Nat.mod_self]
  -- Step 6: Build WaterfallCycle.
  obtain ⟨wc, hwc_eq⟩ := waterfallCycle_of_relabeled gc_r hL_r hn hlowVal_r hmover_mod_r
  -- Step 7: Shadow theorem → ¬converges sys_r gc_r.
  have h3bin_r : hasGe3Binary sys_r.rs := h3bin
  have hno_conv_r := shadow_cycle_mirror_theorem wc hn h3bin_r
  rw [hwc_eq] at hno_conv_r
  -- Step 8: Transfer back via contrapositive.
  intro hconv
  have hmem_sym : ∀ c : Config sys.rs, c ∈ gc.configs ↔ c ∈ gc'.configs :=
    fun c => (hmem' c).symm
  have hconv' := (converges_iff_of_mem_iff gc gc' hmem_sym).mp hconv
  have hconv_r := converges_relabel sys σ σ_inv h_inv h_inv2 gc' gc_r
    (fun c => hgc_r_mem c) hconv'
  exact hno_conv_r hconv_r

/-- Proc-index mirror: μ(i) = (n-i) % n. Maps CCW mover pattern to CW. -/
def procMirror {n : Nat} (i : Fin n) : Fin n :=
  ⟨(n - i.val) % n, Nat.mod_lt _ (by have := i.isLt; omega)⟩

theorem procMirror_val {n : Nat} (i : Fin n) :
    (procMirror i).val = (n - i.val) % n := rfl

theorem procMirror_invol {n : Nat} (hn : n ≥ 1) (i : Fin n) :
    procMirror (procMirror i) = i := by
  ext; simp only [procMirror_val]
  by_cases h0 : i.val = 0
  · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
  · rw [Nat.mod_eq_of_lt (by omega : n - i.val < n),
        show n - (n - i.val) = i.val from by omega,
        Nat.mod_eq_of_lt i.isLt]

/-- Mirror swaps left and right: left(μ(i)) = μ(right(i)). -/
theorem procMirror_left_right {n : Nat} (hn : n ≥ 2) (i : Fin n) :
    left (procMirror i) = procMirror (right i) := by
  ext; simp only [procMirror_val, left_val, right_val]
  by_cases h0 : i.val = 0
  · rw [h0, Nat.sub_zero, Nat.mod_self, show 0 + n - 1 = n - 1 from by omega,
        Nat.mod_eq_of_lt (by omega : n - 1 < n),
        Nat.mod_eq_of_lt (by omega : 1 < n),
        Nat.mod_eq_of_lt (by omega : n - 1 < n)]
  · by_cases hlast : i.val = n - 1
    · rw [hlast, show n - (n - 1) = 1 from by omega,
          Nat.mod_eq_of_lt (by omega : 1 < n), show 1 + n - 1 = n from by omega,
          Nat.mod_self, show n - 1 + 1 = n from by omega, Nat.mod_self, Nat.sub_zero,
          Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega : n - i.val < n),
          show n - i.val + n - 1 = (n - i.val - 1) + 1 * n from by omega,
          Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt (by omega : n - i.val - 1 < n),
          Nat.mod_eq_of_lt (by omega : i.val + 1 < n),
          Nat.mod_eq_of_lt (by omega : n - (i.val + 1) < n)]
      omega

/-- Mirror swaps left and right: right(μ(i)) = μ(left(i)). -/
theorem procMirror_right_left {n : Nat} (hn : n ≥ 2) (i : Fin n) :
    right (procMirror i) = procMirror (left i) := by
  have := procMirror_left_right hn (procMirror i)
  rw [procMirror_invol (by omega) i] at this
  rw [this, procMirror_invol (by omega)]

/-- Mirrored ring spec: rs_m.m(i) = rs.m(μ(i)). -/
def mirrorRingSpec (rs : RingSpec) : RingSpec where
  n := rs.n
  n_ge_4 := rs.n_ge_4
  m := fun i => rs.m (procMirror i)
  m_pos := fun i => rs.m_pos (procMirror i)

theorem mirrorRingSpec_n (rs : RingSpec) : (mirrorRingSpec rs).n = rs.n := rfl
theorem mirrorRingSpec_m (rs : RingSpec) (i : Fin rs.n) :
    (mirrorRingSpec rs).m i = rs.m (procMirror i) := rfl

/-- Mirror a config: mirrorConfig(c)(i) = c(μ(i)). Type-safe because
    mirrorRingSpec.m(i) = rs.m(μ(i)) definitionally. -/
def mirrorConfig {rs : RingSpec} (c : Config rs) : Config (mirrorRingSpec rs) :=
  fun i => c (procMirror i)

def unmirrorConfig {rs : RingSpec} (c : Config (mirrorRingSpec rs)) : Config rs :=
  fun i => by
    have : (mirrorRingSpec rs).m (procMirror i) = rs.m (procMirror (procMirror i)) := rfl
    rw [procMirror_invol (by have := rs.n_ge_4; omega)] at this
    exact this ▸ c (procMirror i)

/-- Mirrored system: transition function with L↔R swap.
    sys_m.f(i)(L, S, R) = sys.f(μ(i))(R', S, L') where R', L' are cast appropriately.

    Type analysis:
    - sys_m.f(i) : Fin(rs_m.m(left i)) → Fin(rs_m.m(i)) → Fin(rs_m.m(right i)) → Fin(rs_m.m(i))
    - rs_m.m(left i) = rs.m(μ(left i)) = rs.m(right(μ(i))) [by procMirror_left_right]
    - rs_m.m(right i) = rs.m(μ(right i)) = rs.m(left(μ(i)))  [by procMirror_right_left]
    - sys.f(μ(i)) : Fin(rs.m(left(μ(i)))) → Fin(rs.m(μ(i))) → Fin(rs.m(right(μ(i)))) → Fin(rs.m(μ(i)))
    So L input to sys_m ↔ R input to sys (both Fin(rs.m(right(μ(i))))), etc.
    We need casts via procMirror_left_right / procMirror_right_left. -/
def mirrorSystem (sys : System) : System where
  rs := mirrorRingSpec sys.rs
  f := fun i L S R =>
    let μi := procMirror i
    -- Cast L : Fin(rs_m.m(left i)) → Fin(rs.m(right(μi))) for R-input of sys.f(μi)
    -- rs_m.m(left i) = rs.m(μ(left i)), and μ(left i) = right(μi)
    let hL : (mirrorRingSpec sys.rs).m (left i) = sys.rs.m (right μi) := by
      show sys.rs.m (procMirror (left i)) = sys.rs.m (right μi)
      rw [← procMirror_right_left (by have := sys.rs.n_ge_4; omega)]
    let hR : (mirrorRingSpec sys.rs).m (right i) = sys.rs.m (left μi) := by
      show sys.rs.m (procMirror (right i)) = sys.rs.m (left μi)
      rw [← procMirror_left_right (by have := sys.rs.n_ge_4; omega)]
    -- Cast inputs and swap L↔R
    sys.f μi (hR ▸ R) S (hL ▸ L)

/-- A uniform CCW good cycle with length 2n, lowVal = 0, and ≥3 binary procs
    cannot converge.

    The standard WaterfallCycle has indicator d = (j + 2n - i) % (2n) ∈ [1,n],
    which matches the CW mover pattern (proc i fires at step i). For CCW
    (proc i fires at step (n-i)%n), the indicator doesn't match directly.

    **Proof strategy**: Define a proc-index mirror μ(i) = (n-i)%n that maps CCW→CW.
    Build a mirrored system sys_m with rs_m.m(i) = rs.m(μ(i)), mirrored configs,
    and a mirrored GoodCycle gc_m with CW mover pattern. Apply the existing
    `waterfallCycle_of_relabeled` to gc_m, then `shadow_cycle_mirror_theorem`
    to get ¬converges sys_m gc_m. Transfer back via the mirror bijection on configs.

    **Status**: sorry — proc-index mirror construction. The helper definitions
    (procMirror, mirrorRingSpec, mirrorConfig, mirrorSystem) are all proved.
    The remaining work is: (1) build gc_m : GoodCycle (mirrorSystem sys_r),
    (2) verify CW mover pattern + lowVal = 0, (3) apply waterfallCycle_of_relabeled
    + shadow_cycle_mirror_theorem, (4) transfer ¬converges back. -/
private theorem ccw_relabeled_not_converges
    {sys_r : System}
    (gc_r : GoodCycle sys_r)
    (_hL : gc_r.configs.length = 2 * sys_r.rs.n)
    (_hn : sys_r.rs.n ≥ 5)
    (_hlowVal : ∀ (i : Fin sys_r.rs.n),
      ((gc_r.configs.get ⟨0, by omega⟩) i).val = 0)
    (_hmover_mod : ∀ k : Fin gc_r.configs.length,
      (gc_r.moverAt k).val = (sys_r.rs.n - k.val % sys_r.rs.n) % sys_r.rs.n)
    (_h3bin : hasGe3Binary sys_r.rs) :
    ¬converges sys_r gc_r := by
  -- Mirror μ(i) = (n-i)%n converts CCW mover pattern to CW.
  -- Build mirrored system, apply CW waterfall + shadow, transfer back.
  set n := sys_r.rs.n with hn_def
  have hn_pos : 0 < n := by omega
  have hn_ge1 : n ≥ 1 := by omega
  have hn_ge2 : n ≥ 2 := by omega
  set sys_m := mirrorSystem sys_r with hsys_m_def
  -- Step 1: Build mirrored config list.
  set configs_m := gc_r.configs.map (mirrorConfig (rs := sys_r.rs)) with hconfigs_m_def
  have hconfigs_m_ne : configs_m ≠ [] := by
    simp [configs_m, gc_r.nonempty]
  have hconfigs_m_len : configs_m.length = gc_r.configs.length := by
    simp [configs_m]
  -- Helper: mirrorConfig is injective (procMirror is involution).
  have mirrorConfig_inj : Function.Injective (mirrorConfig (rs := sys_r.rs)) := by
    intro c₁ c₂ heq
    funext i
    -- mirrorConfig c = fun j => c (procMirror j), and μ is involution.
    -- heq gives c₁(μ j) = c₂(μ j) for all j. Set j = μ i.
    -- μ(μ i) = i, so c₁ i = c₂ i (modulo dependent type cast).
    have hinv := procMirror_invol hn_ge1 i
    have hm_eq : sys_r.rs.m (procMirror (procMirror i)) = sys_r.rs.m i :=
      congrArg sys_r.rs.m hinv
    have hfun := congrFun heq (procMirror i)
    simp only [mirrorConfig] at hfun
    -- hfun : c₁ (procMirror (procMirror i)) = c₂ (procMirror (procMirror i))
    -- Both sides live in Fin (rs.m (μ(μ i))). Cast to Fin (rs.m i) using hinv.
    -- After `revert hm_eq; rw [hinv]`, the cast becomes trivial.
    -- Two errors: h1 proof is complete after revert+rw, and line 3271.
    -- Simplify: after rw [hinv] in hfun, both sides are at i, but rw fails on deps.
    -- Use: hinv says μ(μ i) = i, so congrArg c₁ hinv gives cast equality.
    -- The cleanest approach: use Fin.ext on values.
    have hval := congrArg Fin.val hfun
    -- hval : (c₁ (μ(μ i))).val = (c₂ (μ(μ i))).val
    -- (c₁ (μ(μ i))).val = (c₁ i).val because μ(μ i) = i (as Fin n)
    -- and rs.m is a function of the Fin n index
    -- μ(μ i) = i, so c₁(μ(μ i)) and c₁(i) have the same .val.
    -- Dependent types make rw/subst tricky. Use clear + subst.
    suffices h : (c₁ i).val = (c₂ i).val from Fin.ext h
    have hval := congrArg Fin.val hfun
    -- hval : (c₁ (μ(μ i))).val = (c₂ (μ(μ i))).val
    -- Need: (c₁ i).val = (c₂ i).val
    -- Since μ(μ i) = i as Fin n, c₁(μ(μ i)) and c₁(i) are the same application.
    -- Use: set j := procMirror (procMirror i), clear everything mentioning i,
    -- then subst hinv.
    -- Actually simpler: just convert using congrArg on the dependent function.
    -- For a dep fn c₁ : (j : Fin n) → Fin (rs.m j), and hinv : μ(μ i) = i,
    -- congrArg (fun j => (c₁ j).val) hinv gives the result.
    have key : ∀ (c : Config sys_r.rs),
        (c (procMirror (procMirror i))).val = (c i).val :=
      fun c => congrArg (fun j => (c j).val) hinv
    rw [← key c₁, ← key c₂]; exact hval
  -- (mirror_unmirror removed — not needed for this proof)
  -- Step 2: Privileged transfer: privileged sys_m (mirrorConfig c) (procMirror i) ↔
  --   privileged sys_r c i.
  -- Proof: sys_m.f(procMirror i)(L_m, S_m, R_m)
  --   = sys_r.f(procMirror(procMirror i))(R_m_cast, S_m, L_m_cast)
  --   = sys_r.f(i)(c(right i), c(i), c(left i))... wait, that's sys_r.f(i)(R, S, L).
  -- Actually mirrorSystem swaps L↔R in the transition, so:
  --   sys_m.f(j)(L, S, R) = sys_r.f(μ(j))(R_cast, S, L_cast)
  -- For j = procMirror i, μ(j) = i, and
  --   L input of sys_m at j is (mirrorConfig c)(left j) = c(μ(left j)) = c(right(μ j)) = c(right i)
  --   R input of sys_m at j is (mirrorConfig c)(right j) = c(μ(right j)) = c(left(μ j)) = c(left i)
  --   S input = (mirrorConfig c)(j) = c(μ j) = c(i)
  -- So sys_m.f(j)(L_m, S_m, R_m) = sys_r.f(i)(R_m_cast, c(i), L_m_cast)
  --   = sys_r.f(i)(c(left i)_cast, c(i), c(right i)_cast) = sys_r.f(i)(c(left i), c(i), c(right i))
  -- (after resolving casts). Hence privileged transfers.
  -- Helper: cast ▸ preserves Fin.val
  have hcast_val : ∀ {m₁ m₂ : Nat} (h : m₁ = m₂) (x : Fin m₁), (h ▸ x).val = x.val := by
    intro m₁ m₂ h x; cases h; rfl
  -- Helper: for a dependent function c and h : j₁ = j₂, (c j₁).val = (c j₂).val
  have hdep_val : ∀ (c : Config sys_r.rs) {j₁ j₂ : Fin n} (_h : j₁ = j₂),
      (c j₁).val = (c j₂).val := by
    intro c _ _ h; exact congrArg (fun j => (c j).val) h
  -- The .val of sys_r.f applied at j₁ with args of matching .val
  -- equals the .val of sys_r.f applied at j₂ when j₁ = j₂.
  have dep_f_val_eq : ∀ {j₁ j₂ : Fin n} (hj : j₁ = j₂)
      (L₁ : Fin (sys_r.rs.m (left j₁))) (S₁ : Fin (sys_r.rs.m j₁)) (R₁ : Fin (sys_r.rs.m (right j₁)))
      (L₂ : Fin (sys_r.rs.m (left j₂))) (S₂ : Fin (sys_r.rs.m j₂)) (R₂ : Fin (sys_r.rs.m (right j₂))),
      L₁.val = L₂.val → S₁.val = S₂.val → R₁.val = R₂.val →
      (sys_r.f j₁ L₁ S₁ R₁).val = (sys_r.f j₂ L₂ S₂ R₂).val := by
    intro j₁ j₂ hj; cases hj; intro L₁ S₁ R₁ L₂ S₂ R₂ hL hS hR
    have : L₁ = L₂ := Fin.ext hL
    have : S₁ = S₂ := Fin.ext hS
    have : R₁ = R₂ := Fin.ext hR
    subst_vars; rfl
  -- mirrorSystem output .val = original system output .val
  have mirrorSystem_f_val : ∀ (c : Config sys_r.rs) (i : Fin n),
      ((mirrorSystem sys_r).f (procMirror i)
        (mirrorConfig c (left (procMirror i)))
        (mirrorConfig c (procMirror i))
        (mirrorConfig c (right (procMirror i)))).val =
      (sys_r.f i (c (left i)) (c i) (c (right i))).val := by
    intro c i
    simp only [mirrorSystem, mirrorConfig]
    have hinv := procMirror_invol hn_ge1 i
    have hleft := procMirror_left_right hn_ge2 i
    have hright := procMirror_right_left hn_ge2 i
    apply dep_f_val_eq hinv
    · rw [hcast_val, hright]
      exact hdep_val c (procMirror_invol hn_ge1 (left i))
    · exact hdep_val c hinv
    · rw [hcast_val, hleft]
      exact hdep_val c (procMirror_invol hn_ge1 (right i))
  have privileged_mirror : ∀ (c : Config sys_r.rs) (i : Fin n),
      privileged sys_m (mirrorConfig c) (procMirror i) ↔ privileged sys_r c i := by
    intro c i
    unfold privileged
    have hinv := procMirror_invol hn_ge1 i
    have hs_val : (mirrorConfig c (procMirror i)).val = (c i).val := by
      simp only [mirrorConfig]; exact hdep_val c hinv
    constructor
    · intro hne heq
      apply hne; apply Fin.ext
      rw [mirrorSystem_f_val c i, congrArg Fin.val heq, hs_val]
    · intro hne heq
      apply hne; apply Fin.ext
      rw [← mirrorSystem_f_val c i, congrArg Fin.val heq, ← hs_val]
  -- Step 3: move transfer: move sys_m (mirrorConfig c) (procMirror i) = mirrorConfig (move sys_r c i)
  have move_mirror : ∀ (c : Config sys_r.rs) (i : Fin n),
      move sys_m (mirrorConfig c) (procMirror i) = mirrorConfig (move sys_r c i) := by
    intro c i
    funext j
    -- LHS: move sys_m (mirrorConfig c) (procMirror i) j
    --     = if j = procMirror i then Fin.cast _ (sys_m.f(μi)(...)) else mirrorConfig c j
    -- RHS: mirrorConfig (move sys_r c i) j = (move sys_r c i) (procMirror j)
    --     = if procMirror j = i then Fin.cast _ (sys_r.f(i)(...)) else c(procMirror j)
    -- Key: j = procMirror i ↔ procMirror j = i
    have hinv_i := procMirror_invol hn_ge1 i
    have hinv_j := procMirror_invol hn_ge1 j
    simp only [move, mirrorConfig]
    by_cases hj : j = procMirror i
    · -- j = procMirror i case
      have hμj : procMirror j = i := by rw [hj, hinv_i]
      rw [dif_pos hj, dif_pos hμj]
      apply Fin.ext
      simp only [Fin.val_cast]
      exact mirrorSystem_f_val c i
    · -- j ≠ procMirror i case
      have hμj : procMirror j ≠ i := by
        intro heq; apply hj; rw [← hinv_j, heq, ← hinv_i, procMirror_invol hn_ge1]
      rw [dif_neg hj, dif_neg hμj]
  -- Step 4: Build the GoodCycle on mirrorSystem.
  let gc_m : GoodCycle sys_m := {
    configs := configs_m
    nonempty := hconfigs_m_ne
    unique_privileged := by
      intro c hc
      simp [configs_m] at hc
      obtain ⟨c₀, hc₀_mem, hc₀_eq⟩ := hc
      subst hc₀_eq
      -- Transfer unique_privileged from gc_r
      obtain ⟨i, hi_priv, hi_unique⟩ := gc_r.unique_privileged c₀ hc₀_mem
      refine ⟨procMirror i, (privileged_mirror c₀ i).mpr hi_priv, ?_⟩
      intro j hj_priv
      -- j is privileged for mirrorConfig c₀ in sys_m
      -- Need: j = procMirror i
      -- procMirror(procMirror j) is privileged for c₀ in sys_r (by privileged_mirror applied to procMirror j)
      -- Wait, we need privileged sys_m (mirrorConfig c₀) j → j = procMirror i
      -- Let j' = procMirror j, then procMirror j' = j
      -- privileged sys_m (mirrorConfig c₀) (procMirror j') → privileged sys_r c₀ j' (by privileged_mirror)
      -- Then j' = i by hi_unique, so j = procMirror i.
      let j' := procMirror j
      have hj'_eq : procMirror j' = j := procMirror_invol hn_ge1 j
      rw [← hj'_eq] at hj_priv
      have hj'_priv := (privileged_mirror c₀ j').mp hj_priv
      have hj'_eq_i := hi_unique j' hj'_priv
      rw [← hj'_eq, hj'_eq_i]
    closed := by
      intro k
      have hk_lt : k.val < gc_r.configs.length := by
        have := k.isLt; simp [configs_m] at this; exact this
      -- gc_r.closed at ⟨k.val, hk_lt⟩ gives mover i with privileged + next = move
      obtain ⟨i, hi_priv, hi_move⟩ := gc_r.closed ⟨k.val, hk_lt⟩
      refine ⟨procMirror i, ?_, ?_⟩
      · -- privileged sys_m (configs_m.get k) (procMirror i)
        have hget : configs_m.get k = mirrorConfig (gc_r.configs.get ⟨k.val, hk_lt⟩) := by
          exact list_get_map gc_r.configs mirrorConfig k.val hk_lt (by simp [configs_m]; exact hk_lt)
        rw [hget]
        exact (privileged_mirror _ i).mpr hi_priv
      · -- configs_m.get (nextIndex configs_m k) = move sys_m (configs_m.get k) (procMirror i)
        have hget_k : configs_m.get k = mirrorConfig (gc_r.configs.get ⟨k.val, hk_lt⟩) := by
          exact list_get_map gc_r.configs mirrorConfig k.val hk_lt (by simp [configs_m]; exact hk_lt)
        -- nextIndex configs_m k has the same .val as nextIndex gc_r.configs ⟨k.val, hk_lt⟩
        have hnext_val : (nextIndex configs_m k).val =
            (nextIndex gc_r.configs ⟨k.val, hk_lt⟩).val := by
          simp [nextIndex, hconfigs_m_len]
        have hnext_lt : (nextIndex configs_m k).val < gc_r.configs.length := by
          rw [hnext_val]; exact (nextIndex gc_r.configs ⟨k.val, hk_lt⟩).isLt
        have hget_next : configs_m.get (nextIndex configs_m k) =
            mirrorConfig (gc_r.configs.get ⟨(nextIndex configs_m k).val, hnext_lt⟩) := by
          exact list_get_map gc_r.configs mirrorConfig _ hnext_lt (by simp [configs_m]; exact hnext_lt)
        have hget_next' : gc_r.configs.get ⟨(nextIndex configs_m k).val, hnext_lt⟩ =
            gc_r.configs.get (nextIndex gc_r.configs ⟨k.val, hk_lt⟩) := by
          congr 1; ext; exact hnext_val
        rw [hget_next, hget_next', hi_move, hget_k, move_mirror]
    distinct := by
      intro j₁ j₂ heq
      have hj₁_lt : j₁.val < gc_r.configs.length := by
        have := j₁.isLt; simp [configs_m] at this; exact this
      have hj₂_lt : j₂.val < gc_r.configs.length := by
        have := j₂.isLt; simp [configs_m] at this; exact this
      have hget₁ := list_get_map gc_r.configs mirrorConfig j₁.val hj₁_lt (by simp [configs_m]; exact hj₁_lt)
      have hget₂ := list_get_map gc_r.configs mirrorConfig j₂.val hj₂_lt (by simp [configs_m]; exact hj₂_lt)
      -- heq : configs_m.get j₁ = configs_m.get j₂
      have heq' : mirrorConfig (gc_r.configs.get ⟨j₁.val, hj₁_lt⟩) =
          mirrorConfig (gc_r.configs.get ⟨j₂.val, hj₂_lt⟩) := by
        rw [← hget₁, ← hget₂]; exact heq
      have hinj := mirrorConfig_inj heq'
      have hdist := gc_r.distinct ⟨j₁.val, hj₁_lt⟩ ⟨j₂.val, hj₂_lt⟩ hinj
      ext
      have := Fin.ext_iff.mp hdist
      exact this
    fair := by
      intro i
      obtain ⟨k, j0, hpriv, hstep, hj0⟩ := gc_r.fair (procMirror i)
      subst j0
      have hk_lt : k.val < configs_m.length := by simpa [configs_m] using k.isLt
      let k_m : Fin configs_m.length := ⟨k.val, hk_lt⟩
      have hget_k : configs_m.get k_m = mirrorConfig (gc_r.configs.get k) := by
        exact list_get_map gc_r.configs mirrorConfig k.val k.isLt hk_lt
      have hnext_val : (nextIndex configs_m k_m).val = (nextIndex gc_r.configs k).val := by
        simp [k_m, nextIndex, hconfigs_m_len]
      have hnext_lt : (nextIndex gc_r.configs k).val < configs_m.length := by
        rw [hconfigs_m_len]
        exact (nextIndex gc_r.configs k).isLt
      have hnext_eq : nextIndex configs_m k_m =
          ⟨(nextIndex gc_r.configs k).val, hnext_lt⟩ := by
        ext
        exact hnext_val
      have hget_next : configs_m.get (nextIndex configs_m k_m) =
          mirrorConfig (gc_r.configs.get (nextIndex gc_r.configs k)) := by
        rw [hnext_eq]
        exact list_get_map gc_r.configs mirrorConfig
          (nextIndex gc_r.configs k).val (nextIndex gc_r.configs k).isLt hnext_lt
      refine ⟨k_m, i, ?_, ?_, rfl⟩
      · rw [hget_k]
        simpa [procMirror_invol hn_ge1 i] using
          (privileged_mirror (gc_r.configs.get k) (procMirror i)).mpr hpriv
      · rw [hget_next, hstep, hget_k]
        simpa [procMirror_invol hn_ge1 i] using
          (move_mirror (gc_r.configs.get k) (procMirror i)).symm
  }
  -- Step 5: gc_m has CW mover pattern.
  -- gc_m.configs IS configs_m definitionally (anonymous constructor)
  have hgc_m_configs : gc_m.configs = configs_m := rfl
  have hL_m : gc_m.configs.length = 2 * n := by
    rw [hgc_m_configs, hconfigs_m_len, _hL]
  -- moverAt for gc_m: at step k, the mover is procMirror(moverAt_r(k))
  -- where moverAt_r(k).val = (n - k%n) % n (CCW pattern).
  -- procMirror maps (n - k%n) % n to (n - (n - k%n) % n) % n = k % n (CW pattern).
  have hmover_m : ∀ k : Fin gc_m.configs.length,
      (gc_m.moverAt k).val = k.val % n := by
    intro k
    have hk_lt : k.val < gc_r.configs.length := by
      have h1 := k.isLt; have h2 := hL_m; rw [_hL]; omega
    have hk_lt_m : k.val < configs_m.length := k.isLt
    have hget_k' : configs_m.get ⟨k.val, hk_lt_m⟩ =
        mirrorConfig (gc_r.configs.get ⟨k.val, hk_lt⟩) :=
      list_get_map gc_r.configs mirrorConfig k.val hk_lt hk_lt_m
    have hget_k : gc_m.configs.get k = mirrorConfig (gc_r.configs.get ⟨k.val, hk_lt⟩) :=
      hget_k'
    have hmover_r_priv := gc_r.moverAt_privileged ⟨k.val, hk_lt⟩
    have hmir_priv : privileged sys_m (gc_m.configs.get k) (procMirror (gc_r.moverAt ⟨k.val, hk_lt⟩)) := by
      rw [hget_k]
      exact (privileged_mirror _ _).mpr hmover_r_priv
    have hmover_eq := gc_m.moverAt_unique k _ hmir_priv
    rw [← hmover_eq, procMirror_val]
    have hmover_r_val := _hmover_mod ⟨k.val, hk_lt⟩
    rw [hmover_r_val]
    -- Goal: (sys_m.rs.n - (n - k.val % n) % n) % sys_m.rs.n = k.val % n
    -- sys_m.rs.n = n definitionally (mirrorRingSpec preserves n)
    change (n - (n - k.val % n) % n) % n = k.val % n
    set kmod := k.val % n with hkmod_def
    have hkmod_lt : kmod < n := Nat.mod_lt _ hn_pos
    by_cases hkmod_zero : kmod = 0
    · rw [hkmod_zero, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega : n - kmod < n),
          show n - (n - kmod) = kmod from by omega,
          Nat.mod_eq_of_lt hkmod_lt]
  -- Step 6: lowVal = 0 for gc_m.
  have hlowVal_m : ∀ (i : Fin n),
      ((gc_m.configs.get ⟨0, by rw [hL_m]; omega⟩) i).val = 0 := by
    intro i
    -- gc_m.configs.get ⟨0, _⟩ = mirrorConfig (gc_r.configs.get ⟨0, _⟩)
    -- (mirrorConfig c₀)(i) = c₀(procMirror i)
    -- c₀(procMirror i).val = 0 by _hlowVal
    have hpos_r : 0 < gc_r.configs.length := by rw [_hL]; omega
    have hpos_m : 0 < configs_m.length := by rw [hconfigs_m_len]; exact hpos_r
    have hget0' : configs_m.get ⟨0, hpos_m⟩ =
        mirrorConfig (gc_r.configs.get ⟨0, hpos_r⟩) :=
      list_get_map gc_r.configs mirrorConfig 0 hpos_r hpos_m
    have hget0 : gc_m.configs.get ⟨0, by rw [hL_m]; omega⟩ =
        mirrorConfig (gc_r.configs.get ⟨0, hpos_r⟩) := hget0'
    rw [hget0]
    simp only [mirrorConfig]
    exact _hlowVal (procMirror i)
  -- Step 7: hasGe3Binary for mirrorRingSpec.
  have h3bin_m : hasGe3Binary (mirrorRingSpec sys_r.rs) := by
    -- binaryCount is preserved under procMirror bijection.
    unfold hasGe3Binary binaryCount
    -- Show filter sets are equal via procMirror (= .map on Finsets).
    -- Strategy: show the mirror filter = original filter .map procMirror, then card_map.
    have hfilter_eq :
        Finset.univ.filter (fun i : Fin n => (mirrorRingSpec sys_r.rs).m i = 2) =
        (Finset.univ.filter (fun i : Fin n => sys_r.rs.m i = 2)).map
          ⟨procMirror, fun a b hab => by
            have := congrArg (procMirror (n := n)) hab
            rwa [procMirror_invol hn_ge1, procMirror_invol hn_ge1] at this⟩ := by
      ext j
      constructor
      · intro hj
        rw [Finset.mem_filter] at hj
        rw [Finset.mem_map]
        -- hj.2 : (mirrorRingSpec sys_r.rs).m j = 2, i.e., sys_r.rs.m(μ j) = 2
        refine ⟨procMirror j, ?_, procMirror_invol hn_ge1 j⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hj.2⟩
      · intro hj
        rw [Finset.mem_map] at hj
        obtain ⟨i, hi, rfl⟩ := hj
        rw [Finset.mem_filter] at hi ⊢
        exact ⟨Finset.mem_univ _, by
          show sys_r.rs.m (procMirror (procMirror i)) = 2
          rw [procMirror_invol hn_ge1]; exact hi.2⟩
    calc (Finset.univ.filter (fun i : Fin n => (mirrorRingSpec sys_r.rs).m i = 2)).card
        = ((Finset.univ.filter (fun i : Fin n => sys_r.rs.m i = 2)).map
            ⟨procMirror, fun a b hab => by
              have := congrArg (procMirror (n := n)) hab
              rwa [procMirror_invol hn_ge1, procMirror_invol hn_ge1] at this⟩).card :=
          congrArg Finset.card hfilter_eq
      _ = (Finset.univ.filter (fun i : Fin n => sys_r.rs.m i = 2)).card := Finset.card_map _
      _ ≥ 3 := _h3bin
  -- Step 8: Build WaterfallCycle on gc_m.
  obtain ⟨wc, hwc_eq⟩ := waterfallCycle_of_relabeled gc_m hL_m _hn hlowVal_m hmover_m
  -- Step 9: Shadow theorem → ¬converges sys_m gc_m.
  have hno_conv_m := shadow_cycle_mirror_theorem wc _hn h3bin_m
  rw [hwc_eq] at hno_conv_m
  -- Step 10: Transfer: converges sys_r gc_r → converges sys_m gc_m.
  -- badStep depends only on config membership.
  -- mirrorConfig bijects gc_r.configs with gc_m.configs.
  -- step sys_r c c' ↔ step sys_m (mirrorConfig c) (mirrorConfig c').
  -- So badStep sys_r gc_r c' c ↔ badStep sys_m gc_m (mirrorConfig c') (mirrorConfig c).
  -- WellFoundedness transfers.
  have converges_mirror : converges sys_r gc_r → converges (mirrorSystem sys_r) gc_m := by
    intro hconv
    unfold converges at *
    -- Map badStep of sys_m back to badStep of sys_r via unmirrorConfig.
    -- unmirrorConfig : Config (mirrorRingSpec rs) → Config rs
    -- mirrorConfig ∘ unmirrorConfig = id (on Config mirrorRingSpec rs)
    -- unmirrorConfig ∘ mirrorConfig = id (on Config rs)
    -- step sys_m c_m c_m' → step sys_r (unmirrorConfig c_m) (unmirrorConfig c_m')
    -- c_m ∈ gc_m.configs ↔ unmirrorConfig c_m ∈ gc_r.configs
    -- Helper: unmirrorConfig (mirrorConfig c) = c
    have unmirror_mirror : ∀ c : Config sys_r.rs,
        unmirrorConfig (mirrorConfig c) = c := by
      intro c; funext i; simp only [unmirrorConfig, mirrorConfig]
      have hinv := procMirror_invol hn_ge1 i
      -- Need: (cast ▸ c(μ(μi))) = c(i)
      -- Since μ(μi) = i, c(μ(μi)) and c(i) have the same .val, and the cast makes types match.
      apply Fin.ext
      rw [hcast_val]
      exact hdep_val c hinv
    -- Helper: mirrorConfig (unmirrorConfig c_m) = c_m
    have mirror_unmirror : ∀ c_m : Config (mirrorRingSpec sys_r.rs),
        mirrorConfig (unmirrorConfig c_m) = c_m := by
      intro c_m; funext i; simp only [mirrorConfig, unmirrorConfig]
      apply Fin.ext
      rw [hcast_val]
      -- Need: (c_m (μ(μi))).val = (c_m i).val
      -- This uses the dependent function .val transport, but for Config of mirrorRingSpec.
      exact congrArg (fun j => (c_m j).val) (procMirror_invol hn_ge1 i)
    -- Membership transfer
    have hmem_iff : ∀ c_m : Config (mirrorRingSpec sys_r.rs),
        c_m ∈ gc_m.configs ↔ unmirrorConfig c_m ∈ gc_r.configs := by
      intro c_m
      constructor
      · intro hc_m
        -- c_m ∈ configs_m = gc_r.configs.map mirrorConfig
        simp only [gc_m, configs_m] at hc_m
        rw [List.mem_map] at hc_m
        obtain ⟨c, hc_mem, hc_eq⟩ := hc_m
        rw [← hc_eq, unmirror_mirror]
        exact hc_mem
      · intro hc
        -- unmirrorConfig c_m ∈ gc_r.configs → c_m ∈ gc_m.configs
        -- c_m = mirrorConfig (unmirrorConfig c_m)
        rw [← mirror_unmirror c_m]
        simp only [gc_m, configs_m]
        rw [List.mem_map]
        exact ⟨unmirrorConfig c_m, hc, rfl⟩
    -- Step transfer: step sys_m c_m c_m' → step sys_r (unmirrorConfig c_m) (unmirrorConfig c_m')
    have step_transfer : ∀ c_m c_m' : Config (mirrorRingSpec sys_r.rs),
        step sys_m c_m c_m' →
        step sys_r (unmirrorConfig c_m) (unmirrorConfig c_m') := by
      intro c_m c_m' ⟨i, hpriv, hmove⟩
      -- i is privileged in sys_m, and c_m' = move sys_m c_m i.
      -- procMirror i is the corresponding proc in sys_r.
      -- We need: privileged sys_r (unmirrorConfig c_m) (procMirror i)
      --   and unmirrorConfig c_m' = move sys_r (unmirrorConfig c_m) (procMirror i)
      refine ⟨procMirror i, ?_, ?_⟩
      · -- privileged sys_r (unmirrorConfig c_m) (procMirror i)
        -- unmirrorConfig c_m = unmirrorConfig c_m
        -- mirrorConfig (unmirrorConfig c_m) = c_m (by mirror_unmirror)
        -- privileged sys_m (mirrorConfig (unmirrorConfig c_m)) i ↔ privileged sys_m c_m i
        -- But privileged_mirror says:
        --   privileged sys_m (mirrorConfig c) (procMirror j) ↔ privileged sys_r c j
        -- We need to go in the other direction: from sys_m privileged to sys_r privileged.
        -- Let c := unmirrorConfig c_m, j := procMirror i.
        -- Then procMirror j = procMirror (procMirror i) = i.
        -- privileged sys_m (mirrorConfig c) (procMirror j) ↔ privileged sys_r c j
        -- LHS = privileged sys_m (mirrorConfig (unmirrorConfig c_m)) i = privileged sys_m c_m i
        -- RHS = privileged sys_r (unmirrorConfig c_m) (procMirror i)
        -- So we need: privileged sys_m c_m i → privileged sys_r (unmirrorConfig c_m) (procMirror i)
        have := (privileged_mirror (unmirrorConfig c_m) (procMirror i)).mp
        rw [procMirror_invol hn_ge1, mirror_unmirror] at this
        exact this hpriv
      · -- unmirrorConfig c_m' = move sys_r (unmirrorConfig c_m) (procMirror i)
        -- c_m' = move sys_m c_m i
        -- move_mirror: move sys_m (mirrorConfig c) (procMirror j) = mirrorConfig (move sys_r c j)
        -- With c := unmirrorConfig c_m, j := procMirror i:
        --   move sys_m (mirrorConfig (unmirrorConfig c_m)) (procMirror (procMirror i))
        --   = mirrorConfig (move sys_r (unmirrorConfig c_m) (procMirror i))
        --   move sys_m c_m i = mirrorConfig (move sys_r (unmirrorConfig c_m) (procMirror i))
        -- So unmirrorConfig c_m' = unmirrorConfig (mirrorConfig (move ...)) = move ...
        rw [hmove]
        have := move_mirror (unmirrorConfig c_m) (procMirror i)
        rw [procMirror_invol hn_ge1, mirror_unmirror] at this
        -- this : move sys_m c_m i = mirrorConfig (move sys_r (unmirrorConfig c_m) (procMirror i))
        rw [this, unmirror_mirror]
    -- badStep transfer
    have hbad_map : ∀ a b : Config (mirrorRingSpec sys_r.rs),
        badStep sys_m gc_m a b →
        badStep sys_r gc_r (unmirrorConfig a) (unmirrorConfig b) := by
      intro a b ⟨hb_not_mem, ha_not_mem, hstep⟩
      refine ⟨?_, ?_, step_transfer b a hstep⟩
      · intro hmem; exact hb_not_mem ((hmem_iff b).mpr hmem)
      · intro hmem; exact ha_not_mem ((hmem_iff a).mpr hmem)
    -- Transfer well-foundedness
    exact WellFounded.intro (fun d => by
      suffices ∀ (x : Config sys_r.rs) (d : Config (mirrorRingSpec sys_r.rs)),
          x = unmirrorConfig d → Acc (badStep sys_r gc_r) x → Acc (badStep sys_m gc_m) d from
        this _ d rfl (hconv.apply _)
      intro x d hxd hacc
      induction hacc generalizing d with
      | intro x _ ih =>
        exact Acc.intro d (fun a hbad => by
          have hbad' := hbad_map a d hbad
          rw [← hxd] at hbad'
          exact ih (unmirrorConfig a) hbad' a rfl))
  -- Step 11: Contrapositive.
  intro hconv
  exact hno_conv_m (converges_mirror hconv)

/-- A uniform CCW good cycle with length 2n cannot converge.

    Symmetric to the CW case. Under uniform CCW, moverAt(k) = left^k(moverAt(0)).
    Rotation aligns moverAt(0) with proc 0, then each proc fires at steps
    (n-i)%n and (n-i)%n + n. The waterfall form uses waterfallCycle_of_relabeled_CCW.

    **Proof structure**: Same as uniformCW_not_converges with:
    1. Rotate gc so moverAt(0) = proc 0.
    2. Value relabel so lowVal = 0.
    3. Establish CCW mover pattern: (gc_r.moverAt k).val = (n - k%n) % n.
    4. Build WaterfallCycle via waterfallCycle_of_relabeled_CCW.
    5. Apply shadow_cycle_mirror_theorem → ¬converges.
    6. Transfer back via converges_iff_of_mem_iff + converges_relabel. -/
private theorem uniformCCW_not_converges
    (gc : GoodCycle sys) (_hCCW : gc.uniformCCW)
    (_hfc_all : ∀ p : Fin sys.rs.n, gc.fireCount p = 2)
    (_hL : gc.configs.length = 2 * sys.rs.n)
    (_hn : sys.rs.n ≥ 5)
    (_h3bin : hasGe3Binary sys.rs) :
    ¬converges sys gc := by
  -- Step 1: Rotate gc so moverAt(0) = proc 0.
  -- For CCW, off = p₀ (not n-p₀ as in CW), because moverAt(j) = (p₀ - j) mod n,
  -- so rotating by p₀ gives moverAt_rot(0) = (p₀ - p₀) mod n = 0.
  let off := (gc.moverAt ⟨0, by rw [_hL]; omega⟩).val
  obtain ⟨gc', hmem', hlen', hmover'⟩ := exists_rotated_goodCycle gc off
  -- Step 2: Define value relabeling.
  let c0 : Config sys.rs := gc'.configs.get ⟨0, by rw [hlen']; rw [_hL]; omega⟩
  let σ : (i : Fin sys.rs.n) → Fin (sys.rs.m i) → Fin (sys.rs.m i) :=
    fun i => swapPerm (c0 i) ⟨0, by have := sys.rs.m_pos i; omega⟩
  -- σ is its own inverse (swapPerm is an involution)
  let σ_inv := σ
  have h_inv : ∀ i x, σ_inv i (σ i x) = x :=
    fun i x => swapPerm_involutive (c0 i) ⟨0, by have := sys.rs.m_pos i; omega⟩ x
  have h_inv2 : ∀ i x, σ i (σ_inv i x) = x := h_inv
  -- Step 3: Build relabeled system and GoodCycle.
  let sys_r := relabelSystem sys σ σ_inv
  obtain ⟨gc_r, hgc_r_configs, hgc_r_mem⟩ :=
    relabeled_goodCycle_exists sys σ σ_inv h_inv h_inv2 gc'
  -- Step 4: lowVal = 0 by construction.
  have hgc_r_len : gc_r.configs.length = gc'.configs.length := by
    rw [hgc_r_configs, List.length_map]
  have hgc_r_pos : 0 < gc_r.configs.length := by rw [hgc_r_len, hlen', _hL]; omega
  have hlowVal_r : ∀ (i : Fin sys_r.rs.n),
      ((gc_r.configs.get ⟨0, hgc_r_pos⟩) i).val = 0 := by
    intro i
    have hlen_pos : 0 < gc'.configs.length := by rw [hlen']; rw [_hL]; omega
    have hne_r : gc_r.configs ≠ [] := gc_r.nonempty
    have hne' : gc'.configs ≠ [] := gc'.nonempty
    have get_zero_eq_head {α : Type} (l : List α) (hne : l ≠ []) (h : 0 < l.length) :
        l.get ⟨0, h⟩ = l.head hne := by
      match l, hne with
      | a :: _, _ => rfl
    have head_map {α β : Type} (l : List α) (f : α → β) (hne : l ≠ [])
        (hne2 : l.map f ≠ []) :
        (l.map f).head hne2 = f (l.head hne) := by
      match l, hne with
      | a :: _, _ => rfl
    have hne_mapped : (gc'.configs.map (relabelConfig sys.rs σ)) ≠ [] := by
      simp [hne']
    rw [get_zero_eq_head gc_r.configs hne_r hgc_r_pos]
    have hhead : gc_r.configs.head hne_r =
        (gc'.configs.map (relabelConfig sys.rs σ)).head hne_mapped := by
      congr 1
    rw [hhead, head_map gc'.configs (relabelConfig sys.rs σ) hne' hne_mapped]
    simp only [relabelConfig]
    rw [← get_zero_eq_head gc'.configs hne' hlen_pos]
    change (swapPerm (c0 i) ⟨0, _⟩ (c0 i)).val = 0
    rw [swapPerm_a]
  -- Step 5: Establish CCW mover pattern.
  have hrs_eq : sys_r.rs = sys.rs := rfl
  have hn_r_eq : sys_r.rs.n = sys.rs.n := rfl
  have hL_r : gc_r.configs.length = 2 * sys_r.rs.n := by
    rw [hn_r_eq, hgc_r_configs, List.length_map, hlen', _hL]
  -- The mover pattern of gc_r: under CCW, moverAt(k) = (n - k%n) % n.
  have hmover_mod_r : ∀ k : Fin gc_r.configs.length,
      (gc_r.moverAt k).val = (sys_r.rs.n - k.val % sys_r.rs.n) % sys_r.rs.n := by
    intro k
    have hk' : k.val < gc'.configs.length := by
      have := k.isLt; omega
    -- The relabeling preserves which proc is privileged at each step
    have hpriv_iff : ∀ (c : Config sys.rs) (p : Fin sys.rs.n),
        privileged sys c p ↔ privileged (relabelSystem sys σ σ_inv) (relabelConfig sys.rs σ c) p := by
      intro c p
      simp only [privileged, relabelSystem, relabelConfig]
      constructor
      · intro h habs
        apply h
        have := congrArg (σ_inv p) habs
        simp only [h_inv] at this
        exact this
      · intro h habs
        apply h
        show σ p (sys.f p (σ_inv (left p) (σ (left p) (c (left p))))
          (σ_inv p (σ p (c p))) (σ_inv (right p) (σ (right p) (c (right p))))) = σ p (c p)
        simp only [h_inv]
        exact congrArg (σ p) habs
    -- gc_r.moverAt k = gc'.moverAt ⟨k.val, hk'⟩ via uniqueness
    have hget_eq : gc_r.configs.get k =
        relabelConfig sys.rs σ (gc'.configs.get ⟨k.val, hk'⟩) := by
      exact list_get_of_eq_map hgc_r_configs k.val k.isLt hk'
    have hpriv_at_k : privileged (relabelSystem sys σ σ_inv) (gc_r.configs.get k)
        (gc'.moverAt ⟨k.val, hk'⟩) := by
      have hpriv_gc' := gc'.moverAt_privileged ⟨k.val, hk'⟩
      rw [hpriv_iff (gc'.configs.get ⟨k.val, hk'⟩) (gc'.moverAt ⟨k.val, hk'⟩)] at hpriv_gc'
      rw [hget_eq]
      exact hpriv_gc'
    have hmover_eq : gc'.moverAt ⟨k.val, hk'⟩ = gc_r.moverAt k :=
      gc_r.moverAt_unique k _ hpriv_at_k
    rw [← hmover_eq]
    -- Now relate gc'.moverAt to (n - k%n) % n using uniformCCW + rotation
    set n' := sys.rs.n with hn_def
    set L := gc.configs.length with hL_def
    have hL2n : L = 2 * n' := _hL
    have hLpos : 0 < L := by omega
    set p₀ := (gc.moverAt ⟨0, by omega⟩).val with hp₀_def
    have hp₀_lt : p₀ < n' := (gc.moverAt ⟨0, by omega⟩).isLt
    -- Under uniformCCW, gc.moverAt ⟨j, _⟩ has val (p₀ + n' - j % n') % n'
    -- because each step goes left: moverAt(k+1) = left(moverAt(k))
    -- left subtracts 1 mod n, so moverAt(k) = (p₀ - k) mod n = (p₀ + n' - k%n') % n'
    have mover_orig : ∀ (j : Nat) (hj : j < L),
        (gc.moverAt ⟨j, hj⟩).val = (p₀ + n' - j % n') % n' := by
      intro j
      induction j with
      | zero =>
        intro hj
        simp only [Nat.zero_mod, Nat.sub_zero]
        have h0eq : (⟨0, hj⟩ : Fin L) = ⟨0, hLpos⟩ := rfl
        rw [h0eq, hp₀_def]
        rw [show p₀ + n' = p₀ + 1 * n' from by ring, Nat.add_mul_mod_self_right]
        exact (Nat.mod_eq_of_lt hp₀_lt).symm
      | succ j' ih =>
        intro hj
        have hj' : j' < L := by omega
        have hccw_j := _hCCW ⟨j', hj'⟩
        have hnext_val : (nextIndex gc.configs ⟨j', hj'⟩).val = (j' + 1) % L := by
          simp [nextIndex, hL_def]
        have hmod_eq : (j' + 1) % L = j' + 1 := Nat.mod_eq_of_lt hj
        have hnext_eq : nextIndex gc.configs ⟨j', hj'⟩ = ⟨j' + 1, hj⟩ := by
          ext; rw [hnext_val, hmod_eq]
        rw [hnext_eq] at hccw_j
        -- hccw_j : gc.moverAt ⟨j'+1, hj⟩ = left (gc.moverAt ⟨j', hj'⟩)
        have := congrArg Fin.val hccw_j
        simp only [left_val] at this
        rw [ih hj'] at this
        rw [this]
        -- ((p₀ + n' - j'%n')%n' + n' - 1) % n' = (p₀ + n' - (j'+1)%n') % n'
        -- Both sides ≡ p₀ - j' - 1 (mod n').
        have hn'_pos : 0 < n' := by omega
        have hjmod : j' % n' < n' := Nat.mod_lt _ hn'_pos
        have hmod_lt : (p₀ + n' - j' % n') % n' < n' := Nat.mod_lt _ hn'_pos
        -- Rewrite subtraction: x + n' - 1 = x + (n' - 1) since n' ≥ 5 > 0
        have h_sub : (p₀ + n' - j' % n') % n' + n' - 1 =
            (p₀ + n' - j' % n') % n' + (n' - 1) := by omega
        rw [h_sub]
        rw [Nat.add_mod ((p₀ + n' - j' % n') % n') (n' - 1) n',
            Nat.mod_mod, ← Nat.add_mod (p₀ + n' - j' % n') (n' - 1) n']
        -- Reduce: p₀ + n' - j'%n' + (n' - 1) = (p₀ + (n'-1) - j'%n') + n'
        have h_rw : p₀ + n' - j' % n' + (n' - 1) =
            (p₀ + (n' - 1) - j' % n') + 1 * n' := by omega
        rw [h_rw, Nat.add_mul_mod_self_right]
        -- Case split on wrap-around
        by_cases hj_wrap : j' % n' = n' - 1
        · -- (j'+1) % n' = 0
          have hj1 : (j' + 1) % n' = 0 := by
            have h1n : 1 % n' = 1 := Nat.mod_eq_of_lt (by omega)
            have : (j' + 1) % n' = (j' % n' + 1 % n') % n' := Nat.add_mod j' 1 n'
            rw [this, h1n, hj_wrap, show n' - 1 + 1 = n' from by omega, Nat.mod_self]
          rw [hj_wrap, hj1]
          have : p₀ + (n' - 1) - (n' - 1) = p₀ := by omega
          rw [this, show p₀ + n' - 0 = p₀ + 1 * n' from by omega, Nat.add_mul_mod_self_right]
        · -- (j'+1) % n' = j'%n' + 1
          have hj_lt : j' % n' < n' - 1 := by omega
          have hj1 : (j' + 1) % n' = j' % n' + 1 := by
            have h1n : 1 % n' = 1 := Nat.mod_eq_of_lt (by omega)
            have : (j' + 1) % n' = (j' % n' + 1 % n') % n' := Nat.add_mod j' 1 n'
            rw [this, h1n, Nat.mod_eq_of_lt (by omega)]
          rw [hj1]
          congr 1
          omega
    -- Combine hmover' with mover_orig (same structure as CW but with CCW formula)
    have hk_hmover := hmover' ⟨k.val, hk'⟩
    have := congrArg Fin.val hk_hmover
    rw [this]
    rw [mover_orig ((k.val + off) % L) (Nat.mod_lt _ hLpos)]
    -- Goal: (p₀ + n' - ((k.val + off) % L) % n') % n' = (n' - k.val % n') % n'
    -- off = p₀ (for CCW), L = 2*n'
    -- Step 1: ((k + p₀) % (2n')) % n' = (k + p₀) % n'
    have hmod_reduce : (k.val + off) % L % n' = (k.val + off) % n' := by
      rw [hL2n]
      exact Nat.mod_mod_of_dvd _ ⟨2, by ring⟩
    rw [hmod_reduce]
    -- Step 2: rewrite (k + p₀) % n' using Nat.add_mod
    -- Goal: (p₀ + n' - (k.val + off) % n') % n' = (n' - k.val % n') % n'
    -- off = p₀, so (k + off) = k + p₀
    -- Suffices: (p₀ + off) % n' = 0 ↔ off ≡ -p₀, but for CCW off = p₀
    -- Instead: subtract p₀ from (k + p₀) by showing the result ≡ (n' - k) mod n'
    -- Use Nat.add_mod to decompose (k + p₀) % n':
    rw [Nat.add_mod k.val off n']
    -- Goal: (p₀ + n' - (k.val % n' + off % n') % n') % n' = (n' - k.val % n') % n'
    -- off = p₀ < n', so off % n' = p₀
    have hoff_mod : off % n' = p₀ := Nat.mod_eq_of_lt hp₀_lt
    rw [hoff_mod]
    -- Goal: (p₀ + n' - (k.val % n' + p₀) % n') % n' = (n' - k.val % n') % n'
    set kmod := k.val % n' with hkmod_def
    have hkmod_lt : kmod < n' := Nat.mod_lt _ (by omega)
    -- Unify n' with sys_r.rs.n (definitionally equal)
    change (p₀ + n' - (kmod + p₀) % n') % n' = (n' - kmod) % n'
    -- Case split on whether kmod + p₀ < n'
    by_cases hsum : kmod + p₀ < n'
    · -- (kmod + p₀) % n' = kmod + p₀
      rw [Nat.mod_eq_of_lt hsum]
      -- Goal: (p₀ + n' - (kmod + p₀)) % n' = (n' - kmod) % n'
      have : p₀ + n' - (kmod + p₀) = n' - kmod := by omega
      rw [this]
    · push_neg at hsum
      -- kmod + p₀ ≥ n', and kmod + p₀ < 2*n', so (kmod + p₀) % n' = kmod + p₀ - n'
      have hsum_lt : kmod + p₀ < 2 * n' := by omega
      rw [show kmod + p₀ = (kmod + p₀ - n') + 1 * n' from by omega,
          Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt (by omega : kmod + p₀ - n' < n')]
      -- Goal: (p₀ + n' - (kmod + p₀ - n')) % n' = (n' - kmod) % n'
      have : p₀ + n' - (kmod + p₀ - n') = 2 * n' - kmod := by omega
      rw [this, show 2 * n' - kmod = (n' - kmod) + 1 * n' from by omega,
          Nat.add_mul_mod_self_right]
  -- Step 6-7: Apply CCW non-convergence (mirror + CW waterfall + shadow).
  have h3bin_r : hasGe3Binary sys_r.rs := _h3bin
  have hno_conv_r := ccw_relabeled_not_converges gc_r hL_r _hn hlowVal_r hmover_mod_r h3bin_r
  -- Step 8: Transfer back via contrapositive.
  intro hconv
  have hmem_sym : ∀ c : Config sys.rs, c ∈ gc.configs ↔ c ∈ gc'.configs :=
    fun c => (hmem' c).symm
  have hconv' := (converges_iff_of_mem_iff gc gc' hmem_sym).mp hconv
  have hconv_r := converges_relabel sys σ σ_inv h_inv h_inv2 gc' gc_r
    (fun c => hgc_r_mem c) hconv'
  exact hno_conv_r hconv_r

/-! ### Step 6c: Uniform direction + full support + pivot → False -/

/-- **Uniform direction with full support at a pivot contradicts convergence.**

    **Proved chain (all in importable files):**
    1. `hdir` → WLOG `gc.uniformCW` (symmetric for CCW).
    2. `fireCount_constant_of_uniformCW` (CycleTypes.lean) →
       `∀ p, gc.fireCount p = gc.fireCount t = 2`.
    3. `sum_fireCount` → `gc.configs.length = 2 * sys.rs.n`.
    4. `totalDisplacement_eq_length_of_uniformCW` → displacement = 2n.
    5. `gc.isSweep` (displacement ≥ 2n).

    **Bridge needed (the sorry):**
    6. Construct `WaterfallCycle` from uniform CW + L = 2n + fire = 2.
       The waterfall form `g_j[i] = v_i iff 1 ≤ (j-i) mod 2n ≤ n` follows
       from: uniform CW means each proc fires at positions i+1 and i+n+1
       (mod 2n), toggling high/low. `highVal i` is the value after first fire.
    7. `shadow_cycle_mirror_theorem wc` (Shadow/Theorem.lean, importable)
       → `¬converges sys gc`. Combined with `_hconv`: False.

    Steps 1–5 are provable from existing lemmas. Step 6 is a construction
    (~50–100 lines): extract `highVal`, verify waterfall indicator form.
    Step 7 is one line. -/
theorem uniform_fullSupport_pivot_false
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (_hbL : sys.rs.m (left t) = 2) (_hbR : sys.rs.m (right t) = 2)
    (_hfull : ∀ p : Fin sys.rs.n, 0 < gc.fireCount p)
    (_hn : sys.rs.n ≥ 9)
    (_hconv : converges sys gc)
    (_hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (_hsub : subThreshold sys.rs) (_h3bin : hasGe3Binary sys.rs)
    (hfc_t : gc.fireCount t = 2)
    (hdir : gc.uniformDirection) :
    False := by
  -- Steps 1-5: derive gc.isSweep from uniformDirection + fireCount t = 2.
  rcases hdir with hCW | hCCW
  · -- Uniform CW case
    have hfc_all : ∀ p : Fin sys.rs.n, gc.fireCount p = 2 := by
      intro p; rw [← hfc_t]; exact fireCount_constant_of_uniformCW gc hCW t p
    -- L = sum of fire counts = 2n
    have hL : gc.configs.length = 2 * sys.rs.n := by
      have hsum := gc.sum_fireCount
      rw [show ∑ p : Fin sys.rs.n, gc.fireCount p =
        ∑ _p : Fin sys.rs.n, 2 from Finset.sum_congr rfl (fun p _ => hfc_all p)] at hsum
      simp at hsum; linarith
    -- Uniform CW + length 2n → ¬converges (via rotation + shadow).
    exact uniformCW_not_converges gc hCW hfc_all hL (by omega) _h3bin _hconv
  · -- Uniform CCW case (symmetric).
    have hfc_all : ∀ p : Fin sys.rs.n, gc.fireCount p = 2 := by
      intro p; rw [← hfc_t]; exact fireCount_constant_of_uniformCCW gc hCCW t p
    have hL : gc.configs.length = 2 * sys.rs.n := by
      have hsum := gc.sum_fireCount
      rw [show ∑ p : Fin sys.rs.n, gc.fireCount p =
        ∑ _p : Fin sys.rs.n, 2 from Finset.sum_congr rfl (fun p _ => hfc_all p)] at hsum
      simp at hsum; linarith
    -- Uniform CCW + length 2n → ¬converges (via rotation + shadow).
    exact uniformCCW_not_converges gc hCCW hfc_all hL (by omega) _h3bin _hconv


end LeanMn
