/-
  LeanMn/LowerBound.lean — proved lower-bound program.

  Re-exports the lower-bound modules that are sorry-free. Everything
  here is part of the paper's proved claims and compiles cleanly under
  the default `lake build LeanMn` target.

  The sink-kernel (SK) modules that are research-in-progress
  (`CloudsTheorem`, `EdgeMajorityB2`, `HammingTube`, `SlabCountingRing`,
  and their dependents) are collected under `LeanMn.Research` and are
  built separately via `lake build LeanMn.Research`.

  Attic subdirectories (`attic/`, `Attic/`) are excluded; they are dead
  code kept for provenance only.
-/

-- Proved LB infrastructure
import LeanMn.LowerBound.CycleTypes
import LeanMn.LowerBound.FireCountNe
import LeanMn.LowerBound.GoodCycleBasics

-- Proved entry-conflict chain (all sorry-free)
import LeanMn.LowerBound.EntryConflict.BinaryParity
import LeanMn.LowerBound.EntryConflict.ContextBridge
import LeanMn.LowerBound.EntryConflict.IsolatedFirings
import LeanMn.LowerBound.EntryConflict.NestedFirings
import LeanMn.LowerBound.EntryConflict.PairedCrossing
import LeanMn.LowerBound.EntryConflict.ProcMinGap
import LeanMn.LowerBound.EntryConflict.TernaryPhaseEC

-- Proved small-n LB chain (delivers M_4 = 24 both directions)
import LeanMn.LowerBound.SmallN.BinaryQ4Core
import LeanMn.LowerBound.SmallN.BinaryQ4Word
import LeanMn.LowerBound.SmallN.BinaryQ4GoodCyclePath
import LeanMn.LowerBound.SmallN.BinaryQ4LBBridge
import LeanMn.LowerBound.SmallN.LB2222

-- Sorry-free SK infrastructure (primitives the research tree builds on)
import LeanMn.LowerBound.SK.Forcing
import LeanMn.LowerBound.SK.SinkKernel
import LeanMn.LowerBound.SK.PartialDet
import LeanMn.LowerBound.SK.SlabCounting
