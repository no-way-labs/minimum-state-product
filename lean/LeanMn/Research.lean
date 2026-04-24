/-
  LeanMn/Research.lean — research-in-progress lower-bound program.

  Re-exports the modules that formalize the sink-kernel (SK) approach
  to the general-n lower bound. These modules state the research
  obligations as theorems but contain `sorry` placeholders where
  proofs are not yet complete.

  Build with: `lake build LeanMn.Research`

  This target is **not** part of the default `lake build` target. It is
  separated to make the open-vs-proved distinction explicit for readers
  of the paper: the default build verifies only the paper's proved
  claims; this target lets readers inspect and build the open research
  state.

  As of 2026-04-23, this tree contains 8 `sorry` placeholders across
  the 4 SK modules below, tracking obligations described in the paper's
  §7 and Appendix K (landscape-detail). The transitively dependent
  modules (`SmallN.CloudsLB`, `LargeN.CloudsLB`) carry no new sorrys
  but compile only with the SK obligations admitted.
-/

-- Primitives shared with the proved tree (re-imported so this file
-- can be built standalone via `lake build LeanMn.Research`):
import LeanMn.LowerBound

-- Open research modules (contain `sorry` placeholders):
import LeanMn.LowerBound.SK.CloudsTheorem
import LeanMn.LowerBound.SK.EdgeMajorityB2
import LeanMn.LowerBound.SK.HammingTube
import LeanMn.LowerBound.SK.SlabCountingRing

-- Dependents of the above (no new sorrys, but transitively research):
import LeanMn.LowerBound.SmallN.CloudsLB
import LeanMn.LowerBound.LargeN.CloudsLB
