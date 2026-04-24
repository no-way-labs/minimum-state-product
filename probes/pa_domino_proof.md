# Entry Conflict for Consecutive Binary NormalForm Residual

## Proof Agent Report

### Problem Statement

Close the `sorry` in `consec_isolated_false` (Sweep.lean, line 312) which needs to produce `False` from:
- `hn : sys.rs.n >= 9`
- `gc : GoodCycle sys`
- `hconv : converges sys gc`
- `hno_safe : !exists q, forall k, ...` (no safe processor)
- `hsub : subThreshold sys.rs`
- `h3bin : hasGe3Binary sys.rs`
- `h3consec : threeConsecutiveBinary sys.rs i`
- `hfc_ri : gc.fireCount (right i) >= 2`
- `hiso : isolated firings at right(i)`
- `hparity : odd parity at a neighbor in min firing gap`
- `phase : TernaryPhase gc (right i)` (extracted phase)
- `!hmech : dispatch fails for this phase`

### Critical Finding: EC-Only Route Is Blocked

**Counterexample.** The mover word `(0,0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1)` with `ms = (3,2,2,2,2,2,2,2,2)` at `n = 9` satisfies ALL hypotheses of `consec_isolated_false` (except possibly `hconv`) and has NO entry conflict at ANY processor.

Verification:
- Product = 768 < 8748 = 4*3^7 (sub-threshold)
- 6 consecutive binary triples (positions 1-2-3 through 6-7-8)
- Every binary proc has fc = 2, isolated, both phases have (J,K) = (1,1)
- Odd parity at both neighbors in every gap
- Dispatch fails for every phase: (1,1) is undispatchable
- No safe processors
- |total displacement| = 18 = 2*9 (is a sweep, barely)
- **Zero entry conflict at all 9 processors**

**Consequence.** `consec_isolated_false` cannot be proved via `entryConflict_impossible` alone. The proof MUST use either `hconv` or additional hypotheses.

### Parity Obstruction at t (Proved)

Even if the sorry could be closed via EC, EC at the middle binary proc t = right(i) is blocked by a fundamental parity argument:

**Theorem.** Under the normalForm residual hypotheses (all phases have J+K >= 1 with at least one odd), the pre-fire non-mover context at proc t can never match any mover context at proc t.

**Proof.** At t-fire k, the mover context is (L_k, S_k, R_k) where S_k = (s0 + k) % 2. In phase k (between t-fires k and k+1), non-mover observations at t have S = (S_k + 1) % 2 = S_{k+1}. For EC: need a mover context at some t-fire j with S_j = S_{k+1}, requiring j equiv k+1 (mod 2), so j - k is odd. Also need L_j = L_k (number of left-fire phases in [k..j-1] is even) and R_j = R_k (number of right-fire phases is even). But the sum of these counts is j - k (odd), and two even numbers sum to even. Contradiction.

This means EC at t would require post-fire non-mover observations (steps after a neighbor fires and before t fires, where another proc fires as mover). In a sweep, such steps may not exist since left(t) fires immediately before t in CW passes and right(t) fires immediately before t in CCW passes.

### Proposed Resolution

#### Option A: Use `hconv` (Recommended)

The `hconv` hypothesis asserts that the system converges. This is a GLOBAL property of the transition functions — not just of the good cycle.

The proof route: show that under the sorry-branch hypotheses, the transition function implied by the good cycle (under not-EC) cannot produce a converging system.

Specifically: under not-EC, transition functions at each processor are well-defined (mover and non-mover contexts are disjoint). But the resulting system has structural properties that prevent convergence. For instance:

1. The phase structure (J,K) = (1,1) for all phases means every gap between consecutive t-fires has exactly one fire of each binary neighbor.
2. This creates a specific joint state trajectory on the binary triple.
3. The trajectory, combined with sub-threshold, may force a non-converging potential landscape.

This approach requires significant new infrastructure around convergence properties.

#### Option B: Restructure the Proof (Strongly Recommended)

The sorry exists because the proof decomposes the sweep-consecutive case as:
```
isolated firings → parity check → phase dispatch → normalForm residual
```

The normalForm residual is a dead end (counterexample exists). Instead, restructure:

**For the sweep case with 3 consecutive binary:**
1. Use the Shadow Orbit construction (already proved for non-consecutive binary).
2. Extend the shadow orbit to consecutive binary.
3. The shadow cycle existence theorem already covers consecutive binary with >= 3 binary processors at sub-threshold product (proved in `shadow_general_n.py`, `cic_shadow_comprehensive.py`).

The computational evidence shows: shadow cycles exist for ALL sub-threshold sweep cycles with >= 3 binary, regardless of consecutive vs non-consecutive placement. The existing non-consecutive shadow orbit proof (`sweep_nonConsecutive_false`) can potentially be generalized.

#### Option C: Strengthen the Dispatch (Not Recommended)

One could try to strengthen `phase_dispatch_ec` to handle the (1,1) case. But (1,1) phases with binary neighbors genuinely don't produce EC at t (from the parity obstruction). So this route fails.

### Status of Shadow Orbit in Lean

`ShadowOrbit.lean` currently has TWO sorrys:
1. `shadow_orbit_gives_shadowTrap` (line 48) — the core construction, sorry'd even for non-consecutive.
2. `nonConsecutive_false` (line 72) — general cycle type wrapper, also sorry'd.

The `hnoncons` hypothesis (non-consecutive) appears in both. To use shadow orbit for consecutive binary:
1. Remove or weaken `hnoncons` from `shadow_orbit_gives_shadowTrap`.
2. The mathematical argument is the same — binary flip shadow works regardless of binary placement.
3. This eliminates `consec_isolated_false` entirely: `sweep_false` can route ALL binary cases through shadow orbit.

### Recommended Action Plan

1. **Immediate**: Mark the sorry with a comment explaining the counterexample and why EC-only routes fail.

2. **Short-term (best path)**: Generalize `shadow_orbit_gives_shadowTrap` to drop `hnoncons`. The mathematical shadow construction works for any placement of >=3 binary at sub-threshold (computationally verified for all n=5..11). Then refactor `sweep_false` to use shadow orbit for both consecutive and non-consecutive, eliminating the entire `consec_isolated_false` theorem and its sorry. This also eliminates the >7400 lines of PhaseExtractionBase infrastructure from the critical path.

3. **Alternative**: If shadow formalization is harder than expected, develop a convergence-based argument using `hconv` for the residual case.

### Key Files

- Sorry location: `./lean/LeanMn/LowerBound/Proof/Sweep.lean` line 312
- Phase infrastructure: `.../EntryConflict/PhaseExtractionBase.lean` (7400+ lines)
- Route document: `.../docs/lean_docs/sweep_consec_normalform_route.md`
- Counterexample: ms=(3,2,...,2), word=(0,0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1), n=9
- Shadow orbit (non-consecutive): `.../LowerBound/Proof/ShadowOrbit.lean`
- Computational shadow verification: `shadow_general_n.py`, `cic_shadow_comprehensive.py`

### Proof Sketch for LE (Shadow Orbit Route)

If pursuing the shadow orbit generalization (recommended), the LE needs:

**Step 1: Generalize shadow_orbit_gives_shadowTrap.**
Remove `hnoncons` from the hypotheses. The core argument is:

Given gc : GoodCycle sys with hsub, h3bin, hsweep:
- Pick two binary procs b1, b2 (exist by h3bin, they need not be non-adjacent).
- Define shadow config: flip c_{b1} and c_{b2} in every good config.
- Show shadow configs are non-good (they differ from all good configs at b1 or b2).
- Show shadow transitions form a closed cycle (privilege maintenance).
- The shadow trap gives |shadow configs| + |good configs| distinct configs.
- For sweep: |good configs| >= 2n. Shadow adds 2n more. Total >= 4n.
- Under subThreshold: product < 4*3^{n-2}. For n >= 9: 4n = 36, product can be up to 8748. So the count argument needs refinement.

Actually, the shadow trap gives `not converges` via: the shadow cycle must also converge, but the shadow configs are non-good (no single privileged proc), so the system gets stuck in a cycle that never reaches a legitimate state. This contradicts convergence.

The formal argument:
1. Shadow configs are reachable from some initial config (via the deterministic dynamics).
2. Shadow dynamics form a cycle (no legitimate state in the cycle).
3. Therefore the system doesn't converge from that initial config.
4. This contradicts `hconv`.

The LE's job: formalize the shadow config construction and the privilege maintenance argument. The latter requires showing that at each step, some processor is privileged in the shadow config (not necessarily the same processor as in the original).

**Step 2: Refactor sweep_false.**
Replace the consecutive-binary case split with a single call to the generalized shadow orbit. The `by_cases h3consec` can be replaced by a direct call to shadow orbit in all cases.

### Summary of Computational Scripts Created

- `pa_domino_explore.py` (Expl 1): Phase-structure EC at t. Found: 0% EC (S-flip blocks it).
- `pa_domino_explore3.py` (Expl 3): Proved parity obstruction theorem algebraically.
- `pa_domino_explore5.py` (Expl 5): Showed sorry branch is NOT vacuous (dispatch always fails when odd parity holds).
- `pa_domino_explore6.py` (Expl 6): EC proc distribution — EC occurs at all proc types, not concentrated at t.
- `pa_domino_explore9.py` (Expl 9): EC at no single proc is universal.
- `pa_domino_final2.py` (Final 2): Verified counterexample satisfies all hypotheses, has 0 EC.
