# Exploration Log: Non-Consecutive Binary Terminal Crossing (Odd Winding)

## Investigation Summary

**Question**: For non-consecutive binary under odd winding, NonConsecutive.lean (1732 lines, sorry-free) proves that two distinct singleton edges exist and at least one crossing is at the terminal step (CL-1). Does this terminal crossing case actually occur? If so, what mechanism gives False?

**Answer**: The terminal crossing case IS non-vacuous (2324 walks at n=6 with all-binary-fc=2 have terminal singletons). However, the cutArc/SupportInterval approach used for the "both internal" case CANNOT be adapted for terminal crossings. The correct proof route is Universal Entry Conflict (UEC), which covers ALL cycle types including odd-winding, regardless of crossing location. The Lean sorry is an architecture issue (circular dependency), not a mathematical gap.

---

## Part 1: Structure of the Lean Code

### What NonConsecutive.lean proves (sorry-free, 1732 lines)

1. **Singleton edge structure** (lines 31-92): Under odd winding, every edge has odd traversal count. Traversal count 1 = singleton edge.

2. **Binary fc=2 implies adjacent singleton** (lines 148-183): If binary proc p fires exactly twice under odd winding, then exactly one of its two adjacent edges is singleton. Proof: sum of left+right traversals = 2*(fc - stay). If both >= 3, sum >= 6, but fc=2 forces sum <= 4.

3. **Two non-adjacent binary give two distinct singletons** (lines 1637-1676): From two non-adjacent binary procs with fc=2, get two distinct singleton edges (edges around different procs, non-overlap guaranteed by non-adjacency).

4. **Both internal crossings -> False** (lines 1121-1142): If both singleton edge crossings happen at steps < CL-1, the cutArc/SupportInterval machinery builds a ReturnCone -> config repeat -> contradiction with distinctness. This is the ~500-line core argument.

5. **At least one terminal** (lines 1144-1162): By contradiction from (4): if both < CL-1, False. So at least one crossing is at step CL-1.

6. **Terminal crossing theorem** (lines 1696-1715): Exports the structural result: two singleton edges exist, one has its crossing at CL-1.

### What is NOT proved

NonConsecutive.lean does NOT derive False from the terminal crossing. The file ends with the structural theorem.

### The actual sorry

The sorry is in `ShadowOrbit.lean` line 72:
```
theorem nonConsecutive_false ... : False := by sorry
```
This is called by `OddWinding.lean` line 169 for the non-consecutive odd-winding case. It uses a completely DIFFERENT approach (shadow construction / binary flip) rather than the cutArc machinery.

### Why UEC was removed

Line 1726-1730: `universal_entry_conflict_nonconsec` was removed to break a circular dependency (NonConsecutive.lean -> CaseObstructions.lean -> GlobalMinGap.lean -> cycle through sorry).

---

## Part 2: Does the Terminal Crossing Case Actually Occur?

**YES.** Computational enumeration at n=6 with binary at {0,2,4} (non-consecutive, sub-threshold product 216 < 324):

| Category | Count |
|----------|-------|
| Total odd-winding walks (CL <= 14) | 16,736 |
| Terminal singleton walks | 4,958 |
| Non-terminal (both internal) | 11,778 |
| All-binary-fc=2 + terminal | 2,324 |
| All-binary-fc=2 + both internal | 4,508 |
| Some binary fc > 2 | 9,904 |

The terminal crossing case is non-vacuous under the full hypothesis set (all binary fc=2, odd winding, non-consecutive binary, sub-threshold).

Example walk: `[0, 1, 2, 1, 1, 1, 0, 1, 2, 3, 4, 4, 5]`, len=13, disp=+6
- Singletons: edge 2-3 (step 8), edge 3-4 (step 9), edge 4-5 (step 11), edge 5-0 (step 12=CL-1, TERMINAL)

---

## Part 3: Why the cutArc Argument Fails for Terminal Crossings

The cutArc argument for two internal crossings (at steps ki < kj, both < CL-1):
1. Define cutArc = procs between edges i and j
2. In interval [ki+1, kj]: all movers in cutArc (no edge crossing leaves the arc)
3. In interval [kj+1, ki] (wrapping): all movers in complement
4. This gives SupportInterval -> ReturnCone -> config repeat -> False

For terminal crossing at step CL-1 with internal crossing at step k:
- Interval [k+1, CL-2]: movers in cutArc (OK so far)
- But step CL-1 crosses the terminal edge, and the mover at CL-1 is at the cutArc boundary
- A cutArc-adjacent proc fires at step CL-1, which is OUTSIDE the interval
- The SupportInterval requires `proper: startStep.val < endStep.val` (line 237 of NonConsecutive.lean)
- The cyclicity (step CL-1 wraps to step 0) means the "outside the interval" portion includes a cutArc proc firing
- The frozen-proc argument breaks: cutArc procs are NOT exclusively firing inside the interval

**Fundamental issue**: The SupportInterval struct captures a LINEAR interval [start, end) with movers in a fixed proc set. The terminal crossing creates a CYCLIC wrap-around that the linear interval formalism cannot express.

---

## Part 4: The Correct Proof Route — Universal Entry Conflict

### Why UEC works

The UEC theorem (BinSCC Exploration 10) proves: for >= 3 non-adjacent binary at sub-threshold product, EVERY good cycle has an entry conflict. Four mechanisms:

1. **Both-Even Return** (M=1, both gaps even): mover context = first non-mover context
2. **Toggle-FR** (any M, >= 3 one-sided firings): corner repetition
3. **Zero-Side EC** (M=1, >= 2 one-sided): boundary conflict
4. **Traversal Return** (M=1, singleton first in (2,1)/(1,2) phase): after singleton fires, non-mover sees mover value

Plus two ring-level lemmas:
- **Parity Obstruction**: n=2k, k odd -> all-fc=3 impossible
- **Ring Alternation**: singleton side alternates at consecutive ternary

### Why UEC is winding-independent

All four mechanisms examine the LOCAL structure of the mover word at binary processors:
- The firing gaps between a binary proc's two firings
- The side (CW/CCW) of approaches and departures
- The parity structure of gap lengths

None depend on the global displacement (winding number). The mechanisms work identically for zero-winding and odd-winding cycles.

### Computational verification

UEC verified with 0 exceptions at:
- n=5: 1,094 cycles (all types)
- n=6: 91,872 cycles (all types, includes odd-winding)
- n=8: 11,520 cycles (all types)

The verification script `binscc_complete_proof.py` enumerates ALL good cycles regardless of winding type.

---

## Part 5: How to Close the Sorry

The sorry in `ShadowOrbit.lean:nonConsecutive_false` should be closed by routing through UEC rather than shadow construction.

### Option A: Re-introduce UEC via non-circular import path (RECOMMENDED)
1. Factor the UEC theorem into its own file (e.g., `UniversalEntryConflict.lean`) that does NOT import from the Proof/ directory
2. Have both `NonConsecutive.lean` and `ShadowOrbit.lean` import from it
3. Replace the shadow-based `nonConsecutive_false` with `entryConflict_impossible gc (uec_theorem ...)`

The circular dependency was: NonConsecutive.lean -> CaseObstructions.lean -> GlobalMinGap.lean -> sorry loop. Breaking the chain at the CaseObstructions import fixes this.

### Option B: Complete the shadow construction (harder)
The shadow orbit approach (flip two non-adjacent binary procs) requires proving privilege maintenance at steps where b1 or b2 is the mover. This is RA-verified (1600/1600 cases) but needs Lean formalization with case analysis on neighbor contexts.

### Option C: Extend cutArc to terminal crossings (hardest, NOT recommended)
Would require a new "cyclic support interval" formalism that handles wrap-around. The linear SupportInterval struct is fundamentally inadequate. This is significantly more work than Options A or B.

---

## Part 6: Key Observations

### The "all binary fc=2" hypothesis
NonConsecutive.lean's terminal crossing theorem requires `hfire2: forall p, isBinary -> gc.fireCount p = 2`. This is the minimal case. When binary fc > 2, additional mechanisms (Toggle-FR) apply. The fc=2 case is the hardest.

### Graph-theoretic structure of terminal walks
In terminal walks, the last step crosses a singleton edge, meaning the walk's endpoint is adjacent to its startpoint on the ring but separated by a singleton edge. This creates a very constrained local geometry: all of steps 1..CL-2 avoid crossing this edge.

### The singleton edge is always near the "sweep" portion
In the examples, the terminal singleton edge tends to be at the boundary between the "sweep" portion (CW traverse) and the "return" portion. E.g., edge 5-0 is terminal when the walk sweeps CW through 0->1->2->3->4->5 and then returns.

---

## Conclusion

1. **Terminal crossing case IS non-vacuous**: 2,324 walks at n=6 with all-binary-fc=2 have terminal singletons.

2. **UEC covers it**: Entry conflict mechanisms are winding-independent. Verified computationally at n=5,6,8 with 0 exceptions across all cycle types.

3. **The cutArc approach CANNOT be adapted**: Terminal crossings break the SupportInterval formalism due to cyclic wrap-around.

4. **Recommended fix**: Re-introduce UEC via non-circular import path. The mathematical content is complete; the sorry is purely an architecture/dependency issue.

Scripts: `noncons_terminal_investigation.py`, `noncons_terminal_deep.py`, `noncons_terminal_ec.py`
