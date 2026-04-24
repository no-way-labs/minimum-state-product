# Pre-SK Lower-Bound Attic — 2026-04-14

This directory holds the Lean lower-bound machinery that was retired
when the SK (sink-kernel) invariant was discovered on 2026-04-14.

**Nothing here is built by Lake.** The attic lives outside `LeanMn/` so
the Lean library never tries to compile it. Files are preserved as text
artifacts only — internal `import` statements will be dangling.

## Why it was retired

The previous LB strategy split the obstruction into four mechanisms
(shadow, entry conflict, palindromic EC, sweep no-pivot non-3CB
residual) and stalled at 2–4 sorrys with no path to closure for the
n ≥ 9 three-consecutive-binary case.

The SK invariant unifies all four mechanisms into one structural
theorem: the binary-cube projection of the sink-kernel of the determined
bad graph contains the canonical 10-edge skeleton. See:

- `docs/lean_docs/sk/sk_invariant_findings_2026-04-14.md` —
  full empirical story
- `docs/lean_docs/lb_sk_restart_plan_2026-04-14.md` —
  the plan that led to this attic move

## Layout

```
pre_sk_2026-04-14/
├── README.md  (this file)
├── lower_bound/
│   ├── ArcConfinement.lean
│   ├── IntervalDisplacement.lean
│   ├── MNU.lean
│   ├── Theorem.lean
│   ├── EntryConflict/   (8 files: BAFWord, BinaryRightCrossing,
│   │                     CyclicContext, IsolatedParityEC,
│   │                     NonConsecutive, NonConsecutiveEC,
│   │                     ParityWalk, PhaseExtractionBase)
│   ├── Obstruction/     (5 files: BadCycleData, Core, GlobalTrap,
│   │                     LocalConflict, NonZeroWinding)
│   ├── Proof/           (9 files: CaseDispatch, H1Uniqueness, OddWinding,
│   │                     Result1, Rotation, SafeProcessor, Sweep,
│   │                     WitnessRotation, ZeroWinding)
│   ├── Shadow/          (Construction, Theorem)
│   └── archive/         (the previous LowerBound/Archive/ subtree —
│                         already-archived earlier work, 35 files)
└── smalln/
    ├── ControllerReuse.lean
    ├── M6AllNormalCore.lean
    ├── M6PhaseFront.lean
    ├── M6Routing.lean
    ├── M6SystemFront.lean
    ├── LowerBound/      (n=5 LB attempt: Arithmetic, Blockers, Core,
    │                     Main, N5Check, N5Data, N5Types)
    └── (orphan docs: M4_NATIVE_DECIDE_HANDOFF.md,
                       N5_RESIDUAL_CENSUS_AUDIT_2026-04-14.md,
                       N5_TAIL_EXACT_2026-04-14.json,
                       SMALLN_NEXT_STEP_DECISION_2026-04-14.md,
                       gen_smalln_lower_bound.py)
```

## What was preserved (NOT in the attic)

The following live in `LeanMn/` and continue to build:

- **All UB machinery**: `Convergence/`, `UpperBound/`, `Main.lean`
  (proves `upper_bound : ∀ n ≥ 4, ∃ sys, ...` modulo 7 sorrys in
  `Convergence/ConstLayerDAG.lean`)
- **n = 4 LB (sorry-free, 0 sorrys)**: `SmallN/LB2222.lean` and its
  transitive dependency closure, namely
  - `LowerBound/CycleTypes.lean`, `FireCountNe.lean`, `GoodCycleBasics.lean`
  - `LowerBound/EntryConflict/{BinaryParity, ContextBridge, IsolatedFirings,
    NestedFirings, PairedCrossing, ProcMinGap, TernaryPhaseEC}.lean`
  - `SmallN/{BinaryQ4Core, BinaryQ4Word, BinaryQ4GoodCyclePath,
    BinaryQ4LBBridge, Defs, Theorem}.lean`
- **n = 4..8 UB convergence**: `SmallN/Cup2Convergence.lean`

## Reviving a file

```bash
# History of a moved file
git log --follow -- lean/attic/pre_sk_2026-04-14/lower_bound/<file>

# Bring it back
git mv lean/attic/pre_sk_2026-04-14/lower_bound/<file> \
       lean/LeanMn/LowerBound/<file>
```

After reviving you'll need to fix any dangling imports — most of the
attic'd files import other attic'd files.
