# Routes to Prove `nonConsecutive_false` (ShadowOrbit.lean)

## Current State

`ShadowOrbit.lean` has **1 sorry** at line 196: the near-mover privilege transfer
in `shadow_has_privileged`. When the mover p is b1, b2, or a neighbor of b1/b2,
the binary flip changes the mover's context, and the proof needs to show some
processor is still privileged in the shadow config. RA-verified 1600/1600 but
the case analysis for Lean formalization is non-trivial (the mover may lose
privilege, and a *specific neighbor* must pick it up -- depends on which binary
proc is adjacent and which direction the flip affects).

The theorem is consumed by:
- `Sweep.lean:342` via `sweep_nonConsecutive_false`
- `OddWinding.lean:169` via `nonConsecutive_false`

Both just call `nonConsecutive_false` directly -- the theorem is cycle-type-agnostic.

---

## Route 1: Fix the Existing Binary Flip Sorry (RECOMMENDED)

**Approach**: Fill `shadow_has_privileged` near-mover case at line 196.

**What exists**:
- Far case is fully proved (lines 184-191)
- `farFromBoth` definition at line 107: p != b1, p != b2, no neighbor is b1/b2
- Near case: `p in {b1, b2, left b1, right b1, left b2, right b2}` (6 subcases)
- For each subcase, need: `exists i, privileged sys (shadowConfig ...) i /\ move gives next shadow`

**What's needed**:
1. Case split on `p = b1`, `p = b2`, `p = left b1`, etc. (at most 6 cases)
2. For `p = b1`: b1 is mover. Shadow flips b1's value. After flip, b1 sees its
   own flipped value -> `f(L, 1-v, R) = 1-v` (b1 is non-privileged in shadow).
   But `left b1` or `right b1` sees the flipped b1 value -> becomes privileged.
   Need: `privileged sys (shadowConfig c b1 b2 hb1 hb2) (left b1)` or `(right b1)`.
3. For `p = left b1` (neighbor of b1): shadow changes b1's value. left(b1)'s
   right neighbor is b1. The context at left(b1) changes at the R position.
   Need case analysis on whether this creates/preserves privilege.
4. The `move` commutation for near-mover is more complex than `move_far_shadow`
   because the mover's context may differ.

**Key difficulty**: The near-mover subcase requires showing that *some specific*
processor becomes privileged, which involves the transition function's behavior
on the flipped context. The RA verification (1600/1600) confirms it works but
the Lean proof needs ~6 subcases x context reasoning.

**Estimated LE effort**: 2-3 sessions. This is plumbing-heavy but mathematically
straightforward. Each subcase is essentially: (a) identify which processor is
privileged in the shadow, (b) show privilege, (c) show the move produces the
right next shadow config.

**Risk**: Medium. The near-mover case involves the transition function at specific
contexts, which may require additional lemmas about how binary values interact
with privilege. The mathematical argument is correct (RA-verified) but encoding
the "a neighbor takes over" logic in Lean could be fiddly.

---

## Route 2: Entry Conflict Route (bypass shadow entirely)

**Approach**: Prove `hasEntryConflict gc` directly from the non-consecutive
hypothesis, then chain through `entryConflict_impossible`.

**What exists**:
- `NonConsecutive.lean` (1732 lines, sorry-free) proves extensive infrastructure:
  - `exists_binary_nonadjacent_pair_of_hasGe3Binary_noThreeConsecutive`
  - Singleton edge theorems for odd-winding cycles
  - `two_singletonEdges_force_final_crossing` (for odd-winding + fc=2 regime)
  - `returnCone_false`, `supportInterval_false` (cycle topology lemmas)
- `entryConflict_impossible` in `GoodCycleBasics.lean` (sorry-free): if
  `hasEntryConflict gc` then `False`
- Archive `GlobalMinGap.lean` has `nonConsecutive_zeroWinding_false` but it takes
  a `hNonConsecCore` callback -- it is tautological (passes `hnoncons` to the callback)

**What's needed**:
A universal entry conflict theorem:
```lean
theorem nonConsecutive_hasEntryConflict
    (hn : sys.rs.n >= 9) (gc : GoodCycle sys)
    (hsub : subThreshold sys.rs) (h3bin : hasGe3Binary sys.rs)
    (hnoncons : neg (exists i, threeConsecutiveBinary sys.rs i)) :
    hasEntryConflict gc
```

This would need to implement the 4-mechanism argument from the Python proofs
(Both-Even Return, Toggle-FR, Zero-Side EC, Traversal Return) plus 2 ring-level
lemmas (Parity Obstruction, Ring Alternation). The header comment of
NonConsecutive.lean describes exactly these mechanisms but the final theorem was
removed due to circular dependency.

**Critical observation**: The removed theorem (`universal_entry_conflict_nonconsec`)
had a circular dep because it imported CaseObstructions -> GlobalMinGap -> back.
But `ShadowOrbit.lean` has NO such dep -- it only imports `MNU` and
`NonConsecutive`. So a new theorem in ShadowOrbit.lean (or a new thin file)
could safely import NonConsecutive and prove `hasEntryConflict -> False`.

**Estimated LE effort**: 4-6 sessions. The 4 mechanisms are individually proved
in Python (`binscc_complete_proof.py`) but none are formalized in Lean. Each
mechanism needs: (a) phase extraction from the mover word, (b) fire count
analysis, (c) context matching. This is a full formalization campaign.

**Risk**: High effort, but mathematically solid (0 exceptions at n=5,6,8).

---

## Route 3: Waterfall Shadow (Shadow/Theorem.lean) for sweep-only

**Approach**: For the sweep case only, promote the good cycle to a
`WaterfallCycle` and use the existing `shadow_cycle_mirror_theorem`.

**What exists**:
- `Shadow/Theorem.lean` exports `shadow_cycle_mirror_theorem`:
  ```lean
  theorem shadow_cycle_mirror_theorem
      (wc : WaterfallCycle sys)
      (hn : sys.rs.n >= 5)
      (h3bin : hasGe3Binary sys.rs) :
      neg (converges sys wc.toGoodCycle)
  ```
  This is sorry-free (uses the sigma-permutation shadow, not binary flip).
- `no_valid_sweep_system` corollary: `WaterfallCycle + n>=5 + 3bin -> False`

**What's needed**:
1. A theorem that converts `GoodCycle sys` with `gc.isSweep` into a
   `WaterfallCycle sys`. This requires showing sweep cycles have waterfall form
   (g_j[i] = v_i iff j in I_i). This is the missing bridge.
2. For odd-winding non-consecutive: this route does NOT apply (not a sweep).
   Would still need a separate argument.

**Note**: `shadow_cycle_mirror_theorem` does NOT require non-consecutive binary
-- it works for ALL binary placements with >=3 binary in a sweep. So it could
replace the sweep case entirely. But `OddWinding.lean:169` still needs a
different route.

**Estimated LE effort**: 3-4 sessions for the sweep->waterfall bridge, plus
Route 1 or 2 still needed for odd-winding.

**Risk**: Partial -- only solves sweep. Not a complete replacement.

---

## Recommendation

**Route 1 (fix the existing sorry)** is the best path:

1. **Minimal disruption**: No new files, no import changes, no architectural risk.
2. **Mathematically verified**: 1600/1600 RA-verified. The mechanism is known.
3. **Scope**: One sorry -> 6 subcases of near-mover privilege transfer.
4. **Covers all cycle types**: sweep + odd-winding in one theorem.

The key challenge is the `move` commutation when the mover is adjacent to a
flipped binary proc. The LE agent should:
- Enumerate the 6 near cases: `p = b1`, `p = b2`, `p = left b1`, `p = right b1`,
  `p = left b2`, `p = right b2`
- For each: identify which processor becomes privileged in the shadow
- Prove privilege (context comparison with `shadowConfig_at_*` lemmas)
- Prove `move` produces the correct next shadow config

Route 2 (entry conflict) is a viable fallback but 2-3x the effort. Route 3
is partial.

## Import Graph Note

`ShadowOrbit.lean` currently imports:
- `LeanMn.LowerBound.MNU` (for ShadowTrap, shadowTrap_not_converges)
- `LeanMn.LowerBound.EntryConflict.NonConsecutive` (for exists_binary_nonadjacent_pair)

No circular dependency risk -- both imports are leaf dependencies.
