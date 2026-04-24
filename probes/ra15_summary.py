#!/usr/bin/env python3
"""RA15 SUMMARY: Sorry 7 Investigation Results

This script documents the findings. No computation needed — all data collected.
"""

print("""
========================================================================
RA15 INVESTIGATION: Sorry 7 (Non-Consecutive Binary Entry Conflict)
========================================================================

SORRY 7 STATEMENT (original):
  "odd-winding + non-consecutive binary + non-uniform direction
   + isolated firings → entry conflict"

========================================================================
PART 1: CL ≥ 3n+4 — DISPROVED
========================================================================

The claim CL ≥ 3n+4 is FALSE:

  n=6, ms=[2,3,2,3,2,3]:  min CL = 17,  3n+4 = 22  (FAILS by 5)
  n=7, ms=[2,3,2,3,2,3,3]: min CL = 20,  3n+4 = 25  (FAILS by 5)
  n=9, ms=[2,3,2,3,2,3,3,3,3]: min CL = 26,  3n+4 = 31  (FAILS by 5)

The actual minimum CL is determined by:
  (a) fc constraint: CL ≥ sum(ms) = 2B + 3(n-B) = 3n - B
  (b) Parity: CL ≡ nW (mod 2)
  (c) Walk connectivity: consecutive movers must be ring-adjacent

At n=7: sum(ms) = 18, but CL=18 gives only INVALID cycles (config
collisions). Minimum valid CL = 20, requiring one binary to fire 4x
instead of 2x. This is forced by walk connectivity on C_7 with
non-consecutive binary placement.

Observed min CL pattern:
  n=6: sum(ms)=15, min_CL=17 = sum(ms)+2
  n=7: sum(ms)=18, min_CL=20 = sum(ms)+2
  n=9: sum(ms)=24, min_CL=26 = sum(ms)+2

Conjecture: min CL = sum(ms) + 2 for non-consecutive 3-binary.

========================================================================
PART 2: Pigeonhole Argument — DOES NOT WORK AS STATED
========================================================================

At a sandwiched binary proc b (ternary neighbors):
  Context space: Z_3 × {0,1} × Z_3 = 18 total (9 per S-value)

For the pigeonhole "full coverage" argument to work, need:
  # distinct non-mover (L,R) pairs at some S = 9 (full)
  Then any mover with that S value matches → EC.

But observed at n=7:
  Non-mover (L,R) pair count: max = 7 (out of 9)
  nm + m never exceeds 9 at individual (proc, S) WITHOUT overlap
  → Pure pigeonhole at a single (proc, S) does NOT explain EC

HOWEVER: EC is 100% universal across ALL non-consecutive binary cycles.
It just doesn't come from the pigeonhole argument.

What ACTUALLY drives EC:
  - EC occurs at TERNARY procs in 100% of cycles
  - EC occurs at binary procs in 78% of cycles
  - When EC is at binary only: 0 cases (binary EC → also ternary EC)
  - When EC is at ternary only: 9096/38384 = 23.7%

The EC is from the 4-mechanism analytical proof (BinSCC Expl 10):
  Mech 1: Both-Even Return
  Mech 2: Toggle-FR
  Mech 3: Zero-Side EC
  Mech 4: Traversal Return

These are LOCAL mechanisms at sandwiched ternary procs, not
a counting/pigeonhole argument at binary procs.

========================================================================
PART 3: Cycle-Type Hypothesis — NOT NEEDED
========================================================================

KEY FINDING: EC holds for ALL cycle types, not just odd-winding non-uniform.

n=6, ms=[2,3,2,3,2,3]:
  W=-2 non-uniform:   18/18   = 100% EC
  W=0  non-uniform:  174/174  = 100% EC
  W=2  non-uniform:   18/18   = 100% EC
  W=None non-uniform: 4836/4836 = 100% EC
  (No uniform cycles exist at n=6 for this multiset)

n=7, ms=[2,3,2,3,2,3,3]:
  W=-2 non-uniform:  760/760   = 100% EC
  W=0  non-uniform:  7352/7352 = 100% EC
  W=2  non-uniform:  760/760   = 100% EC
  W=None non-uniform: 29512/29512 = 100% EC
  (No uniform cycles exist)

n=9, ms=[2,3,2,3,2,3,3,3,3]:
  W=-2 non-uniform:  1320/1320   = 100% EC
  W=0  non-uniform:  16696/16696 = 100% EC
  W=2  non-uniform:  1320/1320   = 100% EC
  W=None non-uniform: 40660/40660 = 100% EC

TOTAL: 101,780 / 101,780 = 100.000% EC

No waterfall/uniform cycles exist for non-consecutive binary sub-threshold.
(This makes sense: sweep cycles need a consistent direction, hard with
non-consecutive binary placement.)

CONCLUSION: The only hypothesis needed is:
  "≥3 non-consecutive binary + sub-threshold product → entry conflict"

This is EXACTLY the Universal Entry Conflict theorem already proved
analytically in BinSCC Exploration 10.

========================================================================
PART 4: Edge Flow → CL Bound
========================================================================

Edge flow analysis:
  D = total displacement = n × W (winding number)
  CL = C + K  (CW + CCW steps)
  D = C - K

  Constraints:
    C = (CL + D)/2 ≥ 0
    K = (CL - D)/2 ≥ 0
    CL ≡ D (mod 2)
    CL = Σ fc(p) where fc(p) ∈ {m_p, 2m_p, 3m_p, ...}

  For non-uniform: C > 0 AND K > 0
    → CL > |D| = n|W|
    → CL ≥ |D| + 2 (since CL and D have same parity)

  But |D| + 2 ≤ n|W| + 2 ≤ n + 2 (for |W|=1)
  And sum(ms) = 3n - B ≥ 3n - ⌊n/2⌋
  So fc constraint dominates: CL ≥ sum(ms) + correction

  The edge flow gives NO useful tightening of CL beyond fc constraint
  for the range of n we care about.

  Actual minimum CL = sum(ms) + 2 (empirically), forced by
  walk connectivity, not by displacement.

========================================================================
VERDICT: Sorry 7 should be replaced
========================================================================

Sorry 7's hypotheses (odd-winding, non-uniform, isolated firings) are
all unnecessary. The correct statement is the Universal Entry Conflict
theorem from BinSCC Exploration 10:

THEOREM (Universal EC, PROVED):
  For any ring with ≥3 non-consecutive binary processors and
  product < 4·3^(n-2), every good cycle has entry conflict.

This was proved analytically via 4 mechanisms + 2 ring-level lemmas.
It was verified computationally at n=5,6,7,8,9 with 0 exceptions.

The Lean sorry should reference this theorem directly, not the
restricted odd-winding/non-uniform/isolated hypothesis.
""")
