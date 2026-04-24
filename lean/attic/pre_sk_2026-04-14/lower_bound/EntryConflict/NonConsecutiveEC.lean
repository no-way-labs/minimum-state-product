/-
  NonConsecutiveEC.lean — Non-consecutive binary lower-bound obstruction

  Under convergence, sub-threshold product, ≥ 3 binary processors, and no
  three consecutive binary processors, derive `False`. This file splits
  the old union-shape `nonConsecutive_false` into two case-specific
  theorems, one for each live caller:

  - `nonConsecutive_sweep_false` — for `Proof/Sweep.lean`, consumes
    `gc.isSweep`. Target route: `BadCycleData → GlobalObstruction.shadowTrap`
    via the Shadow Cycle Mirror Theorem.
  - `nonConsecutive_oddWinding_false` — for `Proof/OddWinding.lean`,
    consumes `gc.isOddWinding`. Target route: line confinement with `±n`
    displacement budget (adapted Branch A technique; the `k=0`
    line-confined sub-case reuses Branch A Sub-lemma 1 verbatim, the
    `k≠0` wrap sub-case is an open theorem-discovery target).

  The `ZeroWinding cw > 0` branch does not use this file — it routes
  through `provider_interval_exists_zw` instead.

  ## Scope warning (from `lb_rewrite_session3_audit.md`)

  The claim "non-consec → hasEntryConflict" is **false** as a universal
  statement at n ≥ 9. Session 2 / Session 3 audit confirmed that:

  - For `ms = (2,3,3,2,3,3,2,3,3)` (all-odd-gap, no pivot), ~3% of
    odd-winding good cycles are EC-free by brute-force context check
    and realizable as genuine `GoodCycle sys` instances.
  - The sweep σ shadow permutation from memory's
    `Shadow Cycle Mirror Theorem` fails fc-divisibility on 100% of those
    residual cycles, so the sweep shadow construction cannot close them
    — but they are odd-winding, so they are not the sweep half's scope.

  See `docs/lean_docs/lb_campaign_2026-04-12/sorry2_nonConsec_split_pa_spec_2026-04-13.md`
  for the full PA spec covering both halves.
-/
import LeanMn.LowerBound.EntryConflict.NonConsecutive
import LeanMn.LowerBound.EntryConflict.NestedFirings
import LeanMn.LowerBound.ArcConfinement
import LeanMn.LowerBound.Obstruction.NonZeroWinding

namespace LeanMn

variable {sys : System}

/-- **Odd-winding arc return classification (M4 plumbing).**

    Under Path A hypotheses for the odd-winding half, extract a binary
    processor `b`, two consecutive fires `a₁ < a₂` of `b` with no `b`
    fires in between, and a classification of the corrected return
    interval `[a₁, a₂)` as an integer multiple of `n`.

    This packages Layer 1 + Layer 2 of the
    `interval_displacement_infrastructure_spec_2026-04-13.md` into the
    shape `nonConsecutive_oddWinding_false` consumes. The subsequent
    case split is on the classification integer `k`:

    - `k = 0` (sub-obligation 3a, empirically vacuous on all-odd-gap),
    - `k ≠ 0` (sub-obligation 3b, the wrap sub-case where the Branch A
      line-confinement adaptation lives).

    Both sub-cases remain an open research step; this helper is pure
    plumbing over existing infrastructure. -/
private theorem oddWinding_arc_return_classification
    (gc : GoodCycle sys)
    (h3bin : hasGe3Binary sys.rs)
    (hodd : gc.isOddWinding) :
    ∃ (b : Fin sys.rs.n) (a₁ a₂ : Fin gc.configs.length),
      isBinary sys.rs b ∧
      a₁.val < a₂.val ∧
      gc.moverAt a₁ = b ∧ gc.moverAt a₂ = b ∧
      (∀ k : Fin gc.configs.length,
        a₁.val < k.val → k.val < a₂.val → gc.moverAt k ≠ b) ∧
      ∃ k : Int, gc.intervalDisplacement a₁.val a₂.val = k * sys.rs.n := by
  classical
  -- Step 1: extract a binary from h3bin.
  have hpos : 0 < (Finset.univ.filter
      (fun i : Fin sys.rs.n => sys.rs.m i = 2)).card := by
    unfold hasGe3Binary binaryCount at h3bin
    omega
  rcases Finset.card_pos.mp hpos with ⟨b, hbmem⟩
  have hbin : isBinary sys.rs b := by
    simpa [isBinary] using (Finset.mem_filter.mp hbmem).2
  -- Step 2: fc b > 0 from odd winding (every edge traversed ≥ 1).
  have hfc_pos : gc.fireCount b > 0 := by
    have h1 := gc.edgeTraversalCount_pos_of_isOddWinding hodd (left b)
    have h2 := gc.edgeTraversalCount_pos_of_isOddWinding hodd b
    have hsum :=
      gc.edgeTraversalCount_left_add_edgeTraversalCount_eq_twice_fireCount_sub_stay b
    omega
  -- Step 3: two distinct fires of b.
  obtain ⟨fa, fb, hab_lt, hfa, hfb⟩ :=
    exists_two_firing_steps gc b hbin hfc_pos
  -- Step 4: shrink to a consecutive pair with no b-fires in between.
  obtain ⟨a₁, a₂, hlt, ha₁, ha₂, hno⟩ :=
    exists_consecutive_firing_pair gc b fa fb hab_lt hfa hfb
  -- Step 5: Layer 2 classifies the return interval modulo n.
  obtain ⟨k_int, hk_eq⟩ :=
    arc_displacement_classification gc b hbin a₁ a₂ ha₁ ha₂ hlt
  exact ⟨b, a₁, a₂, hbin, hlt, ha₁, ha₂, hno, k_int, hk_eq⟩

/-- **Sweep non-consecutive binary → False.**

    Sweep-half of the old `nonConsecutive_false`. Called from
    `sweep_false` (Proof/Sweep.lean) for its non-3CB branch, with
    `gc.isSweep` forwarded.

    **Current proof route**: archive sweep obstruction.
    Reuses the public archive theorem `sweep_obstruction`, which already
    discharges sweep cycles in converging sub-threshold systems. -/
theorem nonConsecutive_sweep_false
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys)
    (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (h3bin : hasGe3Binary sys.rs)
    (hsweep : gc.isSweep)
    (_hnoncons : ¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) :
    False := by
  exact sweep_obstruction hn gc hconv hsub hsweep h3bin

/-- **Odd-winding non-consecutive binary → False.**

    Odd-winding-half of the old `nonConsecutive_false`. Called from
    `oddWinding_false` (Proof/OddWinding.lean) for its non-3CB branch,
    with `gc.isOddWinding` forwarded.

    **Current proof route**: archive odd-winding obstruction.
    Derive `¬gc.uniformDirection` from odd winding + `hasGe3Binary`, then
    invoke `oddWinding_nonUniform_obstruction`. The interval-displacement
    plumbing above is retained as dormant local infrastructure for a future
    de-archived proof if needed. -/
theorem nonConsecutive_oddWinding_false
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys)
    (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (h3bin : hasGe3Binary sys.rs)
    (hodd : gc.isOddWinding)
    (_hnoncons : ¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) :
    False := by
  have hnonunif : ¬gc.uniformDirection :=
    fun hunif => gc.not_uniformDirection_and_isOddWinding_of_hasGe3Binary h3bin ⟨hunif, hodd⟩
  exact oddWinding_nonUniform_obstruction hn gc hconv hsub hodd hnonunif h3bin

end LeanMn
