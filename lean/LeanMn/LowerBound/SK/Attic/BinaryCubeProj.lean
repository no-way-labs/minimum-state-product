/-
  LowerBound/SK/BinaryCubeProj.lean — Binary-cube projection of SK

  Targets doc reference:
    docs/lean_docs/sk/sk_invariant_lean_targets_2026-04-14.md §1, §4
-/
import LeanMn.LowerBound.SK.SinkKernel
import LeanMn.LowerBound.SK.Skeleton

namespace LeanMn.SK

variable {sys : System}

/-- The list of binary positions in the ring (those `i` with
    `sys.rs.m i = 2`), in left-to-right order. -/
def binaryPositions (sys : System) : List (Fin sys.rs.n) :=
  (List.finRange sys.rs.n).filter (fun i => sys.rs.m i == 2)

/-- The 3-binary projection of a configuration: read off the values
    at the **first 3** binary positions (per `binaryPositions`) and
    encode as a `CubeVertex`. Returns `none` if the system has fewer
    than 3 binary positions.

    Encoding: `(b₀, b₁, b₂) ↦ b₀ + 2·b₁ + 4·b₂` to match
    `Skeleton.canonicalSkeletonVertices`. -/
def projectToCube (sys : System) (c : Config sys.rs) : Option CubeVertex := by
  sorry

/-- The 3-cube projection of a finset of configs: the set of cube
    vertices that appear as projections of some config in the set. -/
def projectionVertices (sys : System) (S : Finset (Config sys.rs)) :
    Finset CubeVertex := by
  sorry

/-- The 3-cube projection of the forced edges within `S`: a directed
    edge `u → v` is in the projection iff there exist `c, c' ∈ S` with
    `projectToCube c = some u`, `projectToCube c' = some v`, `u ≠ v`,
    and `c'` is a forced neighbor of `c` under `D`. -/
def projectionEdges (D : DetDict sys) (S : Finset (Config sys.rs)) :
    Finset (CubeVertex × CubeVertex) := by
  sorry

end LeanMn.SK
