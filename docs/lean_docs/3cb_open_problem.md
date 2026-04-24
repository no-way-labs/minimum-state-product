# The 3CB Drainage Bottleneck — Open Problem

## Status

Date: 2026-04-09
Status: Open research problem. No known proof mechanism.
Blocks: Sweep.lean:312, OddWinding.lean:153

## The Problem

**Theorem (conjectured):** For n ≥ 9 processors on a ring with 3 consecutive
binary processors (3CB) at positions {i, i+1, i+2} and sub-threshold state
product (< 4·3^(n-2)), no valid self-stabilizing token ring exists.

**What "valid" means:** liveness (every config has a privileged proc), mutual
exclusion (good configs have exactly 1 privileged), closure (good→good),
convergence (every bad config eventually drains to the good cycle), fairness
(every proc fires on the good cycle).

**The gap:** The obstruction mechanism is unknown. All standard proof
techniques have been ruled out.

## What We Know

### The phase transition

| n | 3CB valid system exists? | M_n | Witness ms |
|---|--------------------------|-----|-----------|
| 4 | Yes (19 systems) | 24 | (2,2,2,3) |
| 5 | Yes | 96 | (2,2,2,3,4) |
| 6 | Yes | 288 | (2,2,2,4,3,3) |
| 7 | Yes | 864 | (3,2,2,2,3,4,3) |
| 8 | **No** (768+ constructions fail) | 2592 | (2,2,3,4,3,3,2,3) — non-3CB |
| 9 | **No** (sub-threshold forces) | 8748 | (2,3,3,3,3,3,3,3,2) — non-3CB |

The transition occurs between n=7 and n=8. At n≤7, 3CB systems exist at
the minimum product M_n. At n≥8, the optimal witness avoids 3CB.

### The obstruction is convergence

At n=8 with ms=(2,2,2,3,3,3,3,4), product=2592=M_8:
- Liveness: ✓ (every config has a privileged proc)
- Mutual exclusion + closure: ✓ (fair good cycles exist, typically 42 good configs)
- **Convergence: ✗** (384-528 recurrent bad states in SCCs)

The system CAN build a good cycle. It CANNOT drain all bad configs into it.
Bad configs form persistent cycles (recurrent SCCs) that trap the system
forever.

### The context bottleneck

Proc i+1 (middle of the 3CB block) has both neighbors binary:
- Context space: {0,1}^3 = 8 triples
- Toggle constraint: (a,b,c) privileged → (a,1-b,c) not privileged
- At most 4 mover triples (one from each pair)
- |M| = 4 contradicts hfull → |M| ≤ 3
- Each triple appears at P_rest = Π_{j∉{i,i+1,i+2}} m_j configs

P_rest grows exponentially with n:

| n | P_rest (all ternary) | Total configs | 8-context budget |
|---|----------------------|---------------|------------------|
| 5 | 12 | 96 | 12 configs/context |
| 7 | 108 | 864 | 108 configs/context |
| 8 | 324 | 2592 | 324 configs/context |
| 9 | 972 | 7776 | 972 configs/context |

The 8-context budget is FIXED. The configs-per-context grows as 3^(n-3).
At some point, the fixed-width bottleneck can't handle the flow.

## What Has Been Ruled Out

### Entry conflict (EC)

1. **No sandwiched ternary exists** with exactly 3 binary procs. The
   allNormalFormFalse2 argument needs a ternary proc with both neighbors
   binary. With 3CB at {i,i+1,i+2}: no such proc exists (i+1 has both
   neighbors binary but is itself binary; boundary ternary procs i-1
   and i+3 have only one binary neighbor each).

2. **Long one-sided phases are impossible** near binary blocks. The
   locality constraint (next_mover_is_local) forces gap=2 for any
   J=1,K=0 (or K=1,J=0) phase at ANY proc adjacent to the binary block.
   Verified computationally: 0 long one-sided phases in 6477 target
   phases across 15000 random mover words.

3. **Constant-triple EC is blocked** by the M/N partition. The mover
   triple at step s always differs from the constant non-mover triple
   (the last neighbor fire at s-1 changes the context).

### Shadow traps

4. **Simple binary flip** (flip procs i and i+2): privilege is maintained
   at every step (100% at n=5,6,7,8) but orbit closure fails. PA proved
   the endpoint case requires the flipped proc to fire again immediately,
   which isn't guaranteed. The escape invariant (orbit stays outside good
   cycle) can't be maintained after the first non-commuting step.

5. **Forced-entry shadow** (shift one value, follow mover entries):
   0/180 success at n=5. The mover-entry table doesn't cover all shadow
   contexts. Orbits get stuck (no matching entry) or re-enter the good
   cycle.

6. **Alternative shadows** (flip middle binary, shift ternary, flip all 3):
   0 shadow traps across all variants and starting phases. At n=5 the
   system IS valid, so convergence holds and no shadow trap can exist.

### Structural reductions

7. **WaterfallCycle reduction**: sweep does not force cycle length = 2n,
   uniform direction, or waterfall value pattern. The sorry-free
   shadow_cycle_mirror_theorem cannot be applied.

8. **3CB-specific convergence argument**: 3CB does NOT universally force
   convergence failure. Valid 3CB systems exist at n=5,6,7. The argument
   must use n≥8 (or n≥9) specifically.

## The Drainage Bottleneck Conjecture

**Conjecture:** For n ≥ 8 (or n ≥ 9) with 3CB and sub-threshold product,
the 8-context bottleneck at the middle binary proc creates a drainage
failure: the bad-config graph has recurrent SCCs that cannot be eliminated
by any choice of transition tables.

**Intuition:** Each of the 8 contexts at proc i+1 controls P_rest configs.
The good cycle drains at most ~2n configs per cycle traversal. With P_rest
growing as 3^(n-3) and the drainage rate bounded by O(n), at large enough n
the inflow of bad configs to the bottleneck exceeds the drainage capacity.

**Formalization challenge:** This needs to be an argument about ALL possible
transition table assignments, showing that no matter how the 16 possible
response functions at proc i+1 are chosen (and no matter how the other
procs' rules are set), some bad configs always form cycles.

## Clues

### The Gouda-Haddix connection

The "Alternator" paper (Gouda & Haddix, Distrib. Comput. 2007) proves
convergence of the alternator via directed acyclicity of the privilege
graph. For 4CB (4 consecutive binary), a response-function-count
obstruction is known: no consistent good cycle exists. The 3CB case sits
between 4CB (impossible) and 2CB-non-consecutive (possible).

### The n=8 data

At n=8, ms=(2,2,2,3,3,3,3,4):
- 768 mixed-sweep constructions: ALL have recurrent bad SCCs (384-528
  recurrent bad states, 147 or 75 SCCs)
- Greedy local search reduced SCCs from 147 to 3, never to 0
- n=7→n=8 transplant (19,683 exhaustive slice search): 0 valid systems
- Random mutation (5000 trials): 0 valid systems

The best construction achieves 384 recurrent bad states in 75 SCCs.
The worst has 528 in 147 SCCs. The recurrent states are ~15-20% of all
configs.

### The M_5 witness structure

The valid n=5 3CB system (ms=(2,2,2,3,4)) avoids the bottleneck by:
- Non-minimal cycle length (18 vs 2n=10)
- Non-uniform fire counts (proc 3 fires 6 times, proc 0 fires 2)
- Bidirectional edge usage (CW and CCW traversals of some edges)
- Near-saturation of the context space (18 mover entries out of ~30 possible)

At small n, the context space is small enough relative to the total
configs that the good cycle can saturate it. At large n, the context
space at proc i+1 stays fixed at 8 while the total configs grow
exponentially.

## Suggested Attack Vectors

1. **Privilege graph cycle analysis** (Gouda-Haddix style): show that the
   bad-config privilege graph must contain directed cycles when
   P_rest ≥ some threshold.

2. **Pigeonhole on the 8-context budget**: with |M| ≤ 3 mover triples and
   P_rest · |M| privileged configs at proc i+1, show that the non-proc-1
   drainage paths can't handle the load.

3. **Response function exhaustion**: enumerate all 16 possible response
   functions at proc i+1, and for each show that some bad SCC must exist
   given the sub-threshold product constraint.

4. **Two-proc coupling**: analyze the coupled response functions at procs
   i and i+2 (each has one binary neighbor) and show their interaction
   with proc i+1's bottleneck creates unavoidable cycles.

5. **Information-theoretic**: the 8-context bottleneck can encode at most
   3 bits of state about the rest of the ring. With n-3 ternary procs
   contributing log2(3^(n-3)) ≈ 1.58(n-3) bits of state, the bottleneck
   loses information, making it impossible to route all bad configs
   correctly.

## Files

- This document: `lean/docs/3cb_open_problem.md`
- RA scripts: `probes/ra_shadow_m5.py`, `probes/ra_shadow_consec.py`,
  `probes/ra_forced_entry_consec.py`, `probes/ra_alt_shadows.py`,
  `probes/ra_boundary_ternary_ec.py`, `probes/ra_3cb_transition.py`
- PA reports: `probes/pa_shadow_consec_proof.md`,
  `probes/pa_shadow_consec_v2.md`, `probes/pa_3cb_convergence.md`
- Archived: `LeanMn/LowerBound/Archive/NormalFormEC.lean`
