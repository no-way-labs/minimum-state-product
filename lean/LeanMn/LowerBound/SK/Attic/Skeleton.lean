/-
  LowerBound/SK/Skeleton.lean — The canonical 10-edge skeleton (T3 stub)

  Targets doc reference:
    docs/lean_docs/sk/sk_invariant_lean_targets_2026-04-14.md §1, §3 (T3), §0.5

  This is the **only** file in the SK proof chain where `decide` on
  theorem content is permitted, per the §0.5 ground rules: the 10 edges
  and 8 vertices are explicit, n-independent, and verifiable by eye.
-/
import LeanMn.Basic

namespace LeanMn.SK

/-- A vertex of the 3-cube `{0,1}^3`, encoded as `Fin 8` via
    `(b₀, b₁, b₂) ↦ b₀ + 2·b₁ + 4·b₂`. -/
abbrev CubeVertex : Type := Fin 8

/-- The 8 vertices of the 3-cube. -/
def canonicalSkeletonVertices : List CubeVertex :=
  [0, 1, 2, 3, 4, 5, 6, 7]

/-- The 10 directed edges of the canonical skeleton on the 3-cube.
    First 6 entries: the reverse middle 6-cycle (Hamiltonian cycle on
    the weight-1 + weight-2 layer, in the reverse direction).
    Last 4 entries: the pole attachments (one in/out edge per pole,
    each connecting a single middle vertex to the pole). -/
def canonicalSkeletonEdges : List (CubeVertex × CubeVertex) :=
  -- reverse middle 6-cycle
  [ (6, 4),   -- 011 → 001
    (4, 5),   -- 001 → 101
    (5, 1),   -- 101 → 100
    (1, 3),   -- 100 → 110
    (3, 2),   -- 110 → 010
    (2, 6),   -- 010 → 011
    -- pole attachments (down-pole = 000, up-pole = 111)
    (4, 0),   -- 001 → 000
    (0, 1),   -- 000 → 100
    (3, 7),   -- 110 → 111
    (7, 6) ]  -- 111 → 011

/-- The 4 pole-attachment edges of the canonical skeleton.

    These are the load-bearing edges for T2: the empirical Phase A
    probe (`probe_sk_witness_template_2026-04-15.py`,
    `docs/sk/sk_witness_template_findings_2026-04-15.md`) showed that
    the 4 pole edges have witnesses in `SK` for **every** sub-threshold
    `ms` with at least 3 binary positions (consecutive or spread),
    while some of the 6 reverse-cycle edges fail in spread placements.

    T2 (`tail_skeleton`) uses only this sub-list. The full 10-edge
    skeleton remains in `canonicalSkeletonEdges` as a structural
    object but is not load-bearing for the lower bound. -/
def canonicalPoleEdges : List (CubeVertex × CubeVertex) :=
  [ (4, 0),   -- 001 → 000
    (0, 1),   -- 000 → 100
    (3, 7),   -- 110 → 111
    (7, 6) ]  -- 111 → 011

/-- A directed graph on `CubeVertex` has no sink iff every vertex
    appears as the source of some edge in the list. -/
def hasNoSink (E : List (CubeVertex × CubeVertex)) : Prop :=
  ∀ v : CubeVertex, ∃ e ∈ E, e.1 = v

instance (E : List (CubeVertex × CubeVertex)) : Decidable (hasNoSink E) := by
  unfold hasNoSink
  infer_instance

/-- T3: the canonical skeleton has no sink — every vertex of the
    3-cube has at least one out-edge in the skeleton.

    **This is the one place in the SK chain where `decide` on theorem
    content is permitted** (§0.5 rule (a)): the object is n-independent,
    fits on a screen, and the proof is a finite verification a reviewer
    can do by eye.

    Proof when implemented: `by decide`. -/
theorem canonical_skeleton_no_sink :
    hasNoSink canonicalSkeletonEdges := by
  sorry

end LeanMn.SK
