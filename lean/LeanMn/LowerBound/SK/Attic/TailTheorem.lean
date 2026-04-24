/-
  LowerBound/SK/TailTheorem.lean — Tail skeleton theorem (T2)

  Targets doc reference:
    docs/lean_docs/sk/sk_invariant_lean_targets_2026-04-14.md §3 (T2), §4

  T2 is the structural heart of the SK proof. Phase A produced this
  signature; the actual proof is Phase C work and is the largest
  single Lean component (estimated 800–1200 lines, plus the girth-2k
  lemma at 400–700 lines).
-/
import LeanMn.LowerBound.SK.Skeleton
import LeanMn.LowerBound.SK.BinaryCubeProj

namespace LeanMn.SK

variable {sys : System}

/-- A system is **sub-threshold** for its ring size iff its state
    product is strictly less than `4 · 3^(n-2)`. The lower bound
    theorem says no sub-threshold system is valid. -/
def SubThreshold (sys : System) : Prop :=
  stateProduct sys.rs < 4 * 3 ^ (sys.rs.n - 2)

instance (sys : System) : Decidable (SubThreshold sys) := by
  unfold SubThreshold
  infer_instance

/-- T2 (refined): tail skeleton theorem — pole-edge form.

    For a sub-threshold system with `n ≥ 9` and at least 3 binary
    positions, the binary-cube projection of `SK(gc)` contains all 4
    canonical **pole-attachment** edges.

    The `n ≥ 9` hypothesis is **load-bearing**, not cosmetic. At
    `n = 5..8` there are valid systems with `k ≥ 3` binary positions
    at sub-`4·3^(n-2)` products (e.g. M_5 witness `ms=(2,2,2,3,4)`
    at product 96 < 108), so the conclusion would contradict their
    validity. The SK approach proves the lower bound only at `n ≥ 9`
    where `M_n = 4·3^(n-2)` is sharp. See the targets doc scope
    correction (top of file) and `probes/probe_sk_threshold_check_2026-04-15.py`.

    This is the load-bearing form of T2. The original 10-edge form
    failed empirically for maximally-spread binary placements (e.g.
    n=7 with binary at {0,3,6}); see
    `docs/sk/sk_witness_template_findings_2026-04-15.md`. The 4-pole
    form is uniform across all binary placements tested and is enough
    to derive `tail_SK_nonempty` (any non-empty edge in the projection
    forces SK non-empty).

    Proof structure: for each of the 4 pole edges, exhibit a witness
    config `c ∈ SK gc` with `projectToCube c = some u` and a forced
    step to some `c' ∈ SK gc` with `projectToCube c' = some v`. The
    witness construction is uniform: `c` lives entirely in the
    `{0,1}`-sub-region of the state space (no value 2 anywhere),
    with one ternary position adjacent to a binary forced and all
    other ternary positions flexible. The analytical template is in
    the findings doc.

    Estimate: 400–700 lines (down from the original 800–1200 for the
    full 10-edge claim — halved because we only need 4 templates). -/
theorem tail_skeleton
    (gc : GoodCycle sys)
    (hn : 9 ≤ sys.rs.n)
    (hsub : SubThreshold sys)
    (hbin : 3 ≤ (binaryPositions sys).length) :
    ∀ e ∈ canonicalPoleEdges,
      e ∈ projectionEdges (detOf gc) (SK gc) := by
  sorry

/-- T2-strong (optional, not load-bearing): for sub-threshold `ms`
    with 3 **consecutive** binary positions, the projection contains
    the full canonical 10-edge skeleton.

    Empirically true for n=5..9 with binary at {0,1,2}. Not used by
    the LB proof; kept as a structural curiosity. The proof would
    require the additional case structure for the 6 reverse-cycle
    edges, which is why we don't make it load-bearing. -/
theorem tail_skeleton_strong
    (gc : GoodCycle sys)
    (hsub : SubThreshold sys)
    (hconsec : True)  -- placeholder for "binary positions are 3 consecutive"
    : ∀ e ∈ canonicalSkeletonEdges,
        e ∈ projectionEdges (detOf gc) (SK gc) := by
  sorry

/-- Corollary of T2 + T3: in the tail regime, `SK(gc)` is non-empty.

    Reason: T2 puts every pole edge in the projection; in particular
    the projection is non-empty, so some bad config in `SK gc`
    projects to the source of a pole edge, hence `SK gc ≠ ∅`.

    The `n ≥ 9` hypothesis is inherited from T2 — see `tail_skeleton`
    above. -/
theorem tail_SK_nonempty
    (gc : GoodCycle sys)
    (hn : 9 ≤ sys.rs.n)
    (hsub : SubThreshold sys)
    (hbin : 3 ≤ (binaryPositions sys).length) :
    (SK gc).Nonempty := by
  sorry

end LeanMn.SK
