# Proof Route for nonConsecutive_false

Date: 2026-04-10
Status: PA analysis complete. Ready for LE implementation.

## Problem
Prove: n >= 9, >=3 binary, no 3 consecutive, sub-threshold, valid good cycle → False.
Current binary flip shadow is BROKEN (7/25 steps fail on M_9 witness).

## Recommended: HYBRID ROUTE (2-3 sessions)

### Part 1: Sweep via WaterfallCycle (1 session, low risk)
Replace `sweep_nonConsecutive_false` to use existing sorry-free infrastructure:
- sweep + sub-threshold + >=3 binary → WaterfallCycle [NEW bridge, ~1 session]
- shadow_cycle_mirror_theorem [sorry-free] → ShadowTrap → ¬converges → False

The ONLY new work: proving sweep + sub-threshold implies WaterfallCycle.

### Part 2: Odd winding terminal crossing (1-2 sessions, medium risk)
NonConsecutive.lean (1732 lines, 0 sorrys) already proves:
- Two non-adjacent binary with fc=2 each generate singleton edges
- If BOTH crossings are internal → False (500+ lines of cutArc infrastructure)
- At least one crossing is at terminal step

The gap: terminal crossing case doesn't yet give False.

Two approaches:
A) Terminal crossing as a different support interval (use existing cutArcPred infrastructure)
B) Terminal crossing → entry conflict at binary (use no_binary_2_cycle + context constraint)

### Part 3: Cleanup (trivial)
Delete broken binaryFlip_shadowTrap from ShadowOrbit.lean. Rewire callers.

## Dead routes
- Option A (fix binary flip shadow): DEAD. Fundamentally broken.
- Option B (full EC formalization): Solid but 4-6 sessions and has scope gap (40% of layouts lack sandwiched ternary).
- WaterfallCycle shadow for odd winding: N/A (WaterfallCycle is sweep-only).

## Key files
- NonConsecutive.lean (1732 lines, 0 sorrys) — singleton edge + cutArc infrastructure
- Shadow/Theorem.lean — sorry-free shadow_cycle_mirror_theorem
- Shadow/Construction.lean — sorry-free shadow formula
- ShadowOrbit.lean — BROKEN, to be replaced
- MNU.lean — ShadowTrap + shadowTrap_not_converges
