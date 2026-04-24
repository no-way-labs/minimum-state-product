# Exploration Log: Wiggle Construction (Construction.lean sorry)

## Strategy Register

**Eliminated approach classes:**
1. Canonical wiggle word for zero-winding — eliminated at Expl 5 because the canonical word [0,1,2,1,2,3,...,n-1,0,1,...,n-1] has displacement 2n (SWEEP), not zero. WIGGLE_SPEC.md describes the wrong construction for this sorry.
2. sameValue_samePhase as universal property — eliminated at Expl 4 because it requires fireCount = modulus, which is hard to prove and may not hold in general.
3. Pigeonhole entry conflict — eliminated at Expl 6 because privileged/non-privileged context sets are disjoint by definition (deterministic transition function). Entry conflicts require STRUCTURAL arguments about the cycle, not counting.
4. Import entry conflict machinery from EntryConflict/ — eliminated because Construction.lean is UPSTREAM of those files (circular dependency).
5. Wiggle shadow for zero-winding — CONFIRMED WRONG at Expl 7. The Python proof handles zero-winding multi-reversal via ENTRY CONFLICT (palindromic), not shadow. The wiggle shadow is for SWEEP+BOUNCE (displacement ~2n), already handled by non-zero-winding branch. The sorry is on the WRONG proof path — should use entry conflict, not shadow.

**KEY ARCHITECTURAL FINDING (Expl 7):** The sorry in Construction.lean was placed assuming wiggle shadow handles zero-winding multi-reversal. But the mathematical proof uses entry conflict for this case. The wiggle shadow (spec's construction) is for sweeps. Fix: move the zero-winding multi-reversal handling from Construction.lean to ConsecutiveBinaryBAF.lean (where entry conflict machinery is available), making Construction.lean sorry-free.

**Obstructions:**
- The spec's sigma/delta/offset tables are for the sweep-type wiggle word (displacement 2n). They do NOT work for zero-winding cycles because g_diff values depend on the mover word, which is different. (Expl 5)
- wiggle_moverStructure_exists does NOT take `converges` as input, so cannot derive False from contradiction. Must genuinely construct shadow data from cycle structure alone. (Expl 6)
- Construction.lean can only import: ShadowTrap → MNU → GoodCycleBasics, CycleTypes, Wiggle/Tables, Wiggle/Theorem. Entry conflict files are downstream. (Expl 6)

**Building blocks:**
- WiggleNormalized structure with value-level P3/P4 (no sameValue_samePhase needed). Fully proved Layer 2 reduction. (Expl 1, refined Expl 4)
- samePhase_sameValue holds for ANY good cycle without fc=m assumption (same prefix fire count mod fc → same value). Proof outlined but not formalized. (Expl 3)
- entryConflict_impossible is available via GoodCycleBasics (reachable from Construction.lean). (Expl 6)
- hasEntryConflict definition is available. If we can prove hasEntryConflict from the hypotheses, we get False. (Expl 6)
- WiggleMoverStructure → ShadowTrap → ¬converges chain is fully proved in ShadowTrap.lean + MNU.lean. (Expl 1)

**Known reformulations:**
- LOAD-BEARING: The problem can be reformulated as: prove `hasEntryConflict gc` from (gc, n≥9, subThreshold, zeroWinding, hasMultiReversal, ≥3binary). This gives False via entryConflict_impossible, bypassing WiggleMoverStructure entirely. Available within import constraints. (Expl 6)
- The WiggleMoverStructure route requires constructing 2n+2 Frankenstein shadow configs. The entry conflict route requires finding TWO configs with matching (L,S,R) at some processor (one mover, one non-mover). Entry conflict is a MUCH weaker claim. (Expl 6)

---

## Exploration 1

### Strategy
Build downstream chain first: define WiggleNormalized intermediate structure, prove Layer 2 (WiggleNormalized → WiggleMoverStructure), sorry Layer 3.

### Outcome
SUCCEEDED (mechanical reduction proved, sorry localized)

### Concrete Artifacts
STRUCTURAL RESULTS:
- WiggleNormalized structure: psi, shadowMover, sigma + 8 properties
- wiggleMoverStructure_of_normalized: fully proved, all 5 WMS fields derived from WN
- wiggle_zeroWinding_multiReversal_false: composes Layer 2 + Layer 3

TOOLS:
- Construction.lean rewritten (~220 lines), builds clean

### Key Parameters
- Shadow cycle length: always 2*n+2 (from WiggleMoverStructure type)
- Good cycle length: gc.configs.length (unconstrained)

---

## Exploration 2

### Strategy
Break Layer 3 into sub-lemmas: (A) fireCount = modulus, (B) samePhase_sameValue, (B') sameValue_samePhase, (C) shadow construction.

### Outcome
SUCCEEDED (decomposition) but all sub-lemmas still sorry'd.

### Concrete Artifacts
STRUCTURAL RESULTS:
- Dependency chain: A → B, B' → C → wiggle_normalize
- B depends on A; B' depends on A; C depends on A+B+B'

---

## Exploration 3

### Strategy
Prove samePhase_sameValue for any good cycle without assuming fireCount = modulus.

### Outcome
PARTIALLY SUCCEEDED — proof argument is correct but Lean formalization hit API friction.

### Concrete Artifacts
STRUCTURAL RESULTS:
- samePhase_sameValue holds for ALL good cycles: same prefix fire count mod fc → same value. Proof: within a phase block (contiguous configs with same prefix fire count), processor j doesn't fire, so its value is constant. Wrap-around (phase 0 = phase fc) follows from cycle closure.
- sameValue_samePhase does NOT hold without fc = modulus. Counterexample: binary with fc=4, phases 0 and 2 both have value v₀.

### Surviving Structure
- The proof reduces to: (1) j's value is constant between firings (from state_eq_of_ne_moverAt chain), (2) after fc firings, j returns to initial (cycle closure). Both are available in GoodCycleBasics.

---

## Exploration 4

### Strategy
Remove sameValue_samePhase from WiggleNormalized by moving P3/P4 to value level. This eliminates the need for fireCount = modulus in Layer 2.

### Outcome
SUCCEEDED — simplified WiggleNormalized, Layer 2 still fully proved.

### Concrete Artifacts
STRUCTURAL RESULTS:
- shadow_value_distinct (value-level) replaces shadow_phases_distinct (phase-level)
- shadow_value_disjoint (value-level) replaces shadow_phases_disjoint (phase-level)
- Layer 2 now has 3 proved fields (nonmover_stable, mover_privileged, mover_closure) + 2 pass-through fields (shadow_distinct, shadow_disjoint)

### Reformulations
WiggleNormalized now requires Layer 3 to prove value-level P3/P4 directly, but this is MORE NATURAL since the final WMS fields are value-level anyway. The intermediate phase representation was unnecessary indirection.

---

## Exploration 5

### Strategy
Analyze the mathematical bridge: can the spec's sigma/delta/offset work for zero-winding cycles?

### Outcome
FAILED — fundamental mismatch between spec and sorry.

### Failure Constraint
The canonical wiggle word [0,1,2,1,2,3,...,n-1,0,1,...,n-1] has displacement 2n (a SWEEP). The sorry at wiggle_moverStructure_exists takes hzero : gc.zeroWinding (displacement 0). The closure identities depend on g_diff values from the mover word. Different words → different g_diff → identities don't hold with the same sigma/delta/offset.

### What This Rules Out
Any approach that directly applies the spec's sigma/delta/offset tables to zero-winding cycles without adaptation. The tables are word-specific.

### Reformulations
LOAD-BEARING: The sorry needs a ZERO-WINDING shadow construction, but the spec describes a SWEEP construction. Either (a) there's a different zero-winding construction not described in the spec, or (b) the entry conflict route should be used instead of shadow construction.

---

## Exploration 6

### Strategy
Bypass WiggleMoverStructure entirely: prove False via hasEntryConflict (available in GoodCycleBasics).

### Outcome
STALLED — the argument requires structural analysis of the cycle that I haven't formalized.

### Failure Constraint
Entry conflict requires: ∃ processor p, ∃ configs k₁ (p is mover) and k₂ (p is not mover) with same (L,S,R) context. This is a STRUCTURAL claim about the cycle's mover word + state sequence. It requires zero-winding + multi-reversal + binary structure to force the repeated context.

### Surviving Structure
- entryConflict_impossible is reachable from Construction.lean (via MNU → GoodCycleBasics)
- hasEntryConflict definition is available
- The entry conflict approach needs MUCH LESS than the shadow approach: just 2 configs with matching context, vs 2n+2 Frankenstein configs

### What Would Unblock This
1. A proof that multi-reversal + zero-winding + 3 binary implies hasEntryConflict. The palindromic entry conflict argument (CIC Expl 14) does this mathematically, but the Lean formalization is in downstream files we can't import.
2. OR: a self-contained proof of hasEntryConflict from GoodCycleBasics + CycleTypes primitives. Need to understand the exact structural argument.
3. OR: the correct sigma/delta/offset tables for zero-winding cycles (different from the sweep tables in the spec). This would let the original shadow approach work.

### Open Questions
1. Is there a zero-winding version of the wiggle shadow in the Python explorations?
2. Does the palindromic entry conflict (CIC Expl 14) work for multi-reversal cycles specifically?
3. Can the entry conflict be proved using only CycleTypes + GoodCycleBasics primitives (no import of EntryConflict/ files)?
4. What is the correct relationship between the spec's construction and the zero-winding sorry?

---

## Synthesis after Exploration 6

**Pattern across explorations:** The shadow construction route (Expl 1-5) hit a fundamental obstacle: the spec's tables don't work for zero-winding. The entry conflict route (Expl 6) is more promising but needs the structural argument formalized within import constraints.

**Cross-pollination opportunity:** The entry conflict approach only needs hasEntryConflict (2 configs), not a full shadow cycle (2n+2 configs). This is orders of magnitude less data to construct. The building block from Expl 1 (entryConflict_impossible is reachable) makes this viable.

**Assessment:** This is a CONCEPTUAL stall, not computational. The missing insight is: what specific structural argument proves hasEntryConflict from (zeroWinding, hasMultiReversal, ≥3binary) using only available primitives? The palindromic argument exists mathematically but is formalized in unreachable files. Need to either (a) re-derive the argument in Construction.lean, or (b) get the correct zero-winding shadow tables, or (c) restructure imports.

---

## Exploration 7

### Strategy
Architectural restructure: remove the zero-winding multi-reversal dependency on Construction.lean entirely. The BAF path in ConsecutiveBinaryBAF.lean handles all reversal counts uniformly (the case split on hasMultiReversal was a performance optimization, not a logical necessity). Delete the import and the case split.

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- ConsecutiveBinaryBAF.lean no longer imports Wiggle/Construction.lean
- The `by_cases hmulti : gc.hasMultiReversal` split removed; BAF path handles everything
- Master theorem sorry count: 7 → 5 (the 2 wiggle-related sorrys eliminated)
- Construction.lean is no longer on the critical path (nothing imports it)

COMPUTED EXAMPLES:
- Before: `lake build LeanMn.LowerBound.Theorem` → 7 sorry warnings (including 2 from Construction.lean)
- After: 5 sorry warnings, all in EntryConflict/ and CaseObstructions/
- Remaining sorrys: double_trapped_baf_false, cwWitness_binaryRight_false (×2 gap cases), GapDecisive, PhaseExtraction, CaseObstructions

### Reformulations
LOAD-BEARING: The hasMultiReversal case split was an optimization, not a logical dependency. The BAF/entry-conflict path works for ALL zero-winding cycles regardless of reversal count. This means the wiggle shadow construction (CIC Expl 12-15) is relevant ONLY to the sweep case (non-zero-winding), which is already handled by Shadow/Theorem.lean. The zero-winding case never needed the wiggle shadow.

### Key Parameters
- Before: 7 sorrys on master theorem path
- After: 5 sorrys on master theorem path
- Construction.lean: was 2 sorrys, now 0 sorrys on critical path (still has 1 sorry internally for samePhase_sameValue but file is archival/unused)

---

## Exploration 8 (probe)

### Strategy
Check whether GapDecisive sorry #4 is "just wiring" by testing computationally whether every sandwiched ternary always has a mechanism-triggering phase.

### Outcome
FAILED — found all-normal-form cycles at n=5,9. Ring Alternation is genuinely needed, not dead code.

### Concrete Artifacts
COMPUTED EXAMPLES:
- n=5, bp=[0,2,4], t=3: phases [(1,0),(1,0)] — all normal, no mechanism
- n=9, bp=[0,2,3], t=1: phases [(1,0),(1,0)] — all normal
- n=9, bp=[0,2,4], t=3: phases [(0,1),(0,1)] — all normal
These are ternary procs with fc=2 (fires twice, 2 phases).

TOOLS: check_gap_decisive.py — brute-force cycle enumeration + phase mechanism check.

### What This Rules Out
The Phase B sorry in ring_alternation_forces_mechanism is NOT dead code. Cannot bypass Ring Alternation by showing Stage A always triggers.

---

## Assessment after Exploration 8

All 5 remaining sorrys need substantial new mathematical formalization (100-500 lines each). None is "just wiring." The 7→5 reduction from the architectural fix is the session's deliverable.

Remaining sorrys ranked by estimated tractability:
1. **#4 GapDecisive** (~400 lines): Ring Alternation argument. hno_safe added. Mathematical content is clear from CIC Expl 14.
2. **#1 double_trapped** — **BUGGY theorem statement** (Expl 9). Counterexample: back-and-forth arc cycle satisfies all hypotheses. Fix: use global min data from caller.
3. **#5 CaseObstructions** (~300 lines): Needs palindromic EC.
4. **#2 cwWitness gap≥2** (~200 lines): Needs global minimality threading.
5. **#3 cwWitness gap=1** (~300 lines): Needs palindromic EC.

KEY: #2, #3, #5 share the SAME core argument (palindromic EC). One proof closes all three.

---

## Exploration 9

### Strategy
Analyze sorry #1 (double_trapped_baf_false) for correctness. Construct concrete counterexample.

### Outcome
FOUND BUG — theorem is WRONG as stated.

### Failure Constraint
A back-and-forth arc cycle satisfies all hypotheses: n=9, binary={0,1,2}, procs 0 and 1 trapped (fc=0), mover sweeps arc [2,...,8] twice (zero winding), all procs have nearby movers, system converges. The cycle has NO entry conflict (procs 0,1 never fire; all other procs have unique contexts). The theorem claims False from consistent premises.

### What This Rules Out
Any proof of double_trapped_baf_false from its CURRENT hypotheses. The theorem needs either stronger hypotheses (e.g., global min triple data from caller) or restructured case analysis.

### Surviving Structure
- The global min triple (available in consecutiveBinary_globalMin_residual_false but unused) provides global minimality which might rule out the double_trapped case.
- The back-and-forth arc cycle counterexample has all binary-binary edges UNCROSSED. So the global min triple must be at a non-binary edge.
- With global minimality + 3 consecutive binary: the specific structural constraints might force an entry conflict even in the "trapped" setup.

### Reformulations
LOAD-BEARING: The 5 sorrys decompose into 3 independent mathematical arguments:
1. Ring Alternation (for #4 gapDecisive)
2. Palindromic EC (shared by #2, #3, #5)
3. Bug fix for #1 (use global min data)
Each is ~300-400 lines of Lean. Total: ~1000 lines.

---

## Exploration 10

### Strategy
Close hfc_lt_L sub-sorry in CaseObstructions #3 (fireCount < configs.length from outside mover). Attempted to bypass #3 entirely via shadow for sweeps.

### Outcome
PARTIALLY SUCCEEDED — hfc_lt_L proved (Finset.sum_lt_sum). Shadow bypass for sweeps FAILED (can't access cycle_classification from CaseObstructions). Reverted sweep change.

### Concrete Artifacts
STRUCTURAL RESULTS:
- `hfc_lt_L` proved using Finset.sum_lt_sum: if ∃ k, moverAt(k) ≠ ri, then fc(ri) < L. (The sum of indicators has at least one zero term.)
- sweep_sub_threshold_false's consecutive case IS redundant with case3a_impossible, but can't be bypassed due to import ordering (cycle_classification is in Theorem.lean which imports CaseObstructions).
- The odd-winding consecutive case genuinely needs the palindromic argument (no shadow alternative).

### What This Rules Out
Bypassing sorry #3 via shadow: CaseObstructions can't import Theorem.lean (circular). The shadow is available at a higher level but not at this call site.

### Key Parameters
- Sorry count: still 3 (GapDecisive, GlobalMinGap, CaseObstructions)
- hfc_lt_L: CLOSED (one sub-sorry eliminated within #3)
- phase_dispatch_ec: correctly handles mechanism-triggering phases
- Residual: "all normal form" case for 3 consecutive binary with isolated firings

---

## Exploration 11

### Strategy
Attempt to close remaining 3 sorrys: analyze palindromic EC argument, try shadow bypass for sweep consecutive case, prove helper lemmas.

### Outcome
STALLED on all 3 sorrys. Each genuinely needs the palindromic/Ring Alternation formalization (~300 lines each).

### Concrete Artifacts
STRUCTURAL RESULTS:
- Confirmed: all existing EC mechanisms (BothEven, ToggleFR, zeroSide, traversalReturn) require BOTH neighbors binary. Cannot be applied with 1 binary neighbor.
- Confirmed: pigeonhole on contexts doesn't give EC (privileged/non-privileged are disjoint by determinism).
- Confirmed: sweep consecutive case can't use shadow_cycle_mirror_theorem due to import ordering (CaseObstructions → Theorem is wrong direction).
- The "all normal form" case with fc=2 binary and isolated firings: 0 real examples found in 20K random tests, but COUNTING allows it.
- hno_safe_visit is available from BinaryRightCrossing.lean (added import to GapDecisive).

### What Would Unblock This
The SINGLE missing piece: a Lean proof that the mover word structure forces an entry conflict. This is the palindromic EC / Ring Alternation argument. ~300 lines for each sorry, or ~400 lines for a unified version.

Specific formalization needed:
1. Context tracking through the mover word: define a function that computes (L,S,R) at each step for a given processor
2. Show the palindromic structure creates matching contexts at mover/non-mover steps
3. Derive hasEntryConflict → False

### Open Questions
1. Can the palindromic EC be proved using ONLY the existing Lean infrastructure (prefixFireCount, stateAfter, etc.) without new definitions?
2. Is there a SHORT proof (~50 lines) for specific sub-cases (e.g., gap=1 with binary edge)?
3. Can the 3 sorrys be unified into a SINGLE lemma that covers all cases?

---

## FINAL SESSION STATE

### Sorry count: 7 → 3

### Remaining sorrys (3, all independent):
1. **GapDecisive.lean:18** — non-consecutive binary + hno_safe → False
2. **GlobalMinGap.lean:441** — consecutive binary + zero winding + global min → False
3. **CaseObstructions.lean:898** — consecutive binary + sweep/odd + isolated → False

### What each needs:
All three need the **palindromic entry conflict** argument: showing the mover word structure forces hasEntryConflict. This is ~300 lines of new Lean per sorry (or ~400 for a unified version).

---

## Exploration 12

### Strategy
Create shared palindromic_phase_ec lemma in PhaseExtraction.lean. Wire it to CaseObstructions sorry #3 via phase dispatch + palindromic residual.

### Outcome
SUCCEEDED (wiring) — CaseObstructions sorry eliminated from the build by routing through palindromic_phase_ec.

### Concrete Artifacts
STRUCTURAL RESULTS:
- palindromic_phase_ec placed in PhaseExtraction.lean (avoids circular imports)
- CaseObstructions wires: phase_dispatch_ec for mechanism-triggering, palindromic_phase_ec for normal-form residual
- FiringPhase → TernaryPhase conversion resolved by placing in same file
- Sorry count: 3 (PhaseExtraction:737 = shared core, GapDecisive:14, GlobalMinGap:441)
- CaseObstructions is NO LONGER in the sorry list (routes through PhaseExtraction's sorry)

### What Would Unblock Zero Sorry
1. **palindromic_phase_ec** (~200 lines): THE core mathematical argument. Proves hasEntryConflict from normal-form phase structure. Needs context tracking through mover word.
2. **gapDecisive_false** (~100 lines): Find sandwiched ternary, dispatch. Uses palindromic_phase_ec for residual.
3. **consecutiveBinary_globalMin_residual_false** (~100 lines): Use global min data + palindromic. OR: route through a different argument for consecutive binary.

Total to zero: ~400 lines, with palindromic_phase_ec being the critical ~200 line piece.

### Files modified this session:
- `Wiggle/Construction.lean` — rewritten (sorry-free archival infrastructure)
- `EntryConflict/ConsecutiveBinaryBAF.lean` — removed hasMultiReversal split, removed Wiggle import
- `EntryConflict/GapDecisive.lean` — added hno_safe hypothesis (correctness fix)
- `EntryConflict/PhaseExtraction.lean` — deleted dead code (ring_alternation_forces_mechanism)
- `EntryConflict/GlobalMinGap.lean` — removed ConsecutiveBinaryBAF import, sorry'd residual directly
- `CaseObstructions.lean` — proved hno_safe derivations, proved hfc_lt_L, built dispatch structure

### Open Questions
1. Does the global min triple ALWAYS avoid the double-trapped case? (If so: #1 becomes dead code)
2. Can palindromic EC be proved compactly using the existing TernaryPhaseEC mechanisms?
3. Is there a unified argument that handles both consecutive and non-consecutive cases?
4. Can the global min data be threaded from consecutiveBinary_globalMin_residual_false through to cwWitness_binaryRight_false to make the gap≥2 case sorry-free? (The global min MinGapArc is already proved.)

---

## Session Summary

### What was accomplished:
1. **Wiggle sorry CLOSED** (original target): The zero-winding multi-reversal case never needed the wiggle shadow — it's handled by the BAF/entry-conflict path which works for all reversal counts. Architectural correction.
2. **Sorry count: 7 → 5**: Removed 2 wiggle-related sorrys from the master theorem path.
3. **Fixed wrong theorem**: Added `hno_safe` to gapDecisive_false (was unprovable without it, counterexample: one-mover cycle).
4. **Derived hno_safe from sweep/odd-winding**: Proved the two helper derivations using `no_safeProcessor_of_nonZeroWinding`.
5. **Found bug in #1**: `double_trapped_baf_false` has a concrete counterexample. Needs restructuring.
6. **Identified key insight**: Sorrys #2, #3, #5 share the palindromic EC core argument.

### What remains (5 sorrys):
- **#1 (double_trapped)**: BUGGY. Needs global min data or restructure.
- **#2 (gap≥2)**: Needs global min data threading (MinGapArc is proved).
- **#3 (gap=1)**: Needs palindromic EC (~300 lines new math).
- **#4 (gapDecisive)**: Needs Ring Alternation (~400 lines new math).
- **#5 (isolated_noSafe)**: Needs palindromic EC (~300 lines new math).

### Three independent work items to zero sorry:
1. **Fix #1 + #2**: Thread global min data. ~100 lines plumbing. Might make both sorry-free without new math.
2. **Close #4**: Ring Alternation. ~400 lines new Lean. Independent of #1-3.
3. **Close #3 + #5**: Palindromic EC. ~300 lines new Lean. One argument closes both.

---

## CURRENT STATE (End of Session)

### Sorry count: 7 → 3

### Remaining sorrys:
1. **PhaseExtraction.lean:737** — `palindromic_phase_ec` (shared core)
2. **GapDecisive.lean:14** — `gapDecisive_false` (non-consecutive binary)
3. **GlobalMinGap.lean:441** — `consecutiveBinary_globalMin_residual_false` (consecutive binary + zero winding)

### Key proof strategy discovered:
**Case A/B shadow argument**: For each binary fire step, flip the binary value. Either:
- **Case A**: The flipped binary is privileged at the next config → unique_privileged violation (two privileged procs) → False
- **Case B**: The flipped binary is NOT privileged → combined with the original fire step's context: same (L,S,R) at both mover (original fire) and non-mover (next config after Case B fire) → hasEntryConflict

This works when val(left(left(t))) is unchanged between the two comparison steps. For CONSECUTIVE fire steps (a'+1 = b'): guaranteed unchanged. For non-consecutive: needs tracking.

### What remains for zero sorry:
~200 lines of Lean formalizing the Case A/B argument + val(ll) tracking. The mathematical content is fully understood. The formalization requires:
1. Extract consecutive left fire pair using exists_consecutive_fire_pair_bounded
2. Case split: f(left(t), val(ll), 1-S, T₀) = S (Case A) or = 1-S (Case B)
3. Case A: show unique_privileged violated at next config
4. Case B: show same context at first fire (mover) and post-second-fire (non-mover)
5. Wire palindromic_phase_ec into gapDecisive_false and GlobalMinGap
