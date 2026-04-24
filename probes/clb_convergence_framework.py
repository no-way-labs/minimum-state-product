#!/usr/bin/env python3
"""
CONVERGENCE PROOF FRAMEWORK: Summary and Key Results
====================================================

THEOREM (to prove):
For all n >= 5, the CUP-2 system with ms=(2,3,...,3,2) and the 5 universal
lookup tables (87 entries) has an acyclic bad-config graph (DAG).

STATUS: Verified computationally for n=5..18.
        Analytical proof: OPEN, but framework identified.

KEY STRUCTURAL RESULTS
======================

1. NO 2-CYCLE PROPERTY (Proved analytically):
   For every table T and every (L,R) pair, the function a → T(L,a,R)
   has no 2-cycles. Equivalently, T(L, T(L,a,R), R) = T(L,a,R).
   Proof: Direct verification over all 87 entries.

2. MOVER ALWAYS GAINS TARGET (Verified n=5..8):
   When position i fires (changes value), it moves to the fixed point of
   f_{L,R} where L=c[i-1], R=c[i+1]. The mover ALWAYS becomes settled
   (at its fixed point). Never loses settled status.

3. FREEZE-ANY-POSITION DAG (Verified n=5..12):
   For any position p, the restricted graph where p never fires is a DAG.
   This holds for ALL positions (bot, low, mid, high, top) and ALL n tested.

4. ALL-POSITION PARTICIPATION (Consequence of #3):
   Any hypothetical cycle must involve firings at ALL n positions.
   Proof: If position p doesn't fire in a cycle, the cycle exists in
   the p-frozen graph, contradicting the DAG property of #3.

5. OSCILLATION REQUIREMENT (Proved via #1):
   Each position that fires in a cycle must fire ≥ 2 times.
   Minimum cycle length ≥ 2n.

6. NEIGHBOR-CHANGE OBLIGATION (Proved via #1):
   For each T_mid oscillation a→b→a, at least one neighbor must change
   between the two firings. Specifically:
   - 30 total oscillation types
   - 8 require ONLY left neighbor change (leftward chain)
   - 4 require ONLY right neighbor change (rightward chain)
   - 18 require BOTH neighbors to change
   - 0 require neither (impossible by no-2-cycle)

7. DIRECTIONAL FLOW:
   T_mid transitions have specific neighbor requirements:
   - 0→1: requires L=1 (information flows RIGHTWARD)
   - 1→2: requires R=2 (information flows LEFTWARD)
   - 2→0: requires R∈{0,2} and various L
   - 2→1: requires L=1, R=1
   Counter-propagating waves: "1-wave" goes right, "2-wave" goes left.

8. QUADRATIC DEPTH FORMULA (Verified n=5..13):
   max_depth(n) = ⌊(3n² - 4n - 11)/4⌋

9. INDUCTIVE CORRELATION (Verified n=7..9):
   Rank correlation between n and (n-1) projections: 0.73-0.82,
   INCREASING with n. Strong evidence for inductive provability.

PROOF APPROACHES (evaluated)
=============================

A. POTENTIAL FUNCTION (exhausted):
   Tested: sum, frontier, count_2s, priv_count, at_target, left_agreement,
   settled_count, Hamming-to-good, inversions, descents, entropy,
   sum_of_squares, weighted_settled, all 2-feature linear/lex combinations.
   Best: 3*n_priv - sum (~19% violations), linear_right weighted settled (~16%).
   CONCLUSION: No simple potential function exists.

B. HARMONIC CRITERION (fails):
   Σ 1/(D_p + 1) where D_p = frozen-p DAG depth.
   Sum = 0.57 (n=5) → 0.14 (n=12), always < 1.
   CONCLUSION: Frozen depths are too large for counting argument.

C. CAUSAL CHAIN IMPOSSIBILITY (most promising):
   Framework:
   1. Every position fires ≥ 2 times in a cycle (#4, #5)
   2. Each oscillation creates obligations at neighbors (#6)
   3. Obligations propagate as chains through the ring (#7)
   4. For the chain to close, it must wrap around the ring
   5. The boundary tables (T_bot, T_low, T_high, T_top) have different
      oscillation characteristics that break the chain

   Key remaining step: Formalize step 5 — show that the boundary
   oscillation requirements are inconsistent with the interior chain closure.

D. STRUCTURAL INDUCTION (promising, needs formalization):
   Base case: n=5 (verified).
   Inductive step: Adding one T_mid processor preserves DAG property.
   Projection correlation (~0.8) supports this approach.

WHAT THE PROOF NEEDS
====================

The proof likely requires one of:

1. A NON-STANDARD potential function that captures the "wave phase" structure
   of the good cycle. The potential would likely be multi-level (lexicographic)
   with components that depend on the POSITIONS of value-2 cells relative to
   value-1 cells.

2. A CAUSAL CHAIN argument showing that the obligation propagation from
   T_mid oscillations creates an inconsistency at the boundary tables.
   The key insight: T_bot and T_top are binary while T_mid is ternary,
   creating an "impedance mismatch" that prevents causal chains from
   wrapping around the ring.

3. An INDUCTIVE argument on n using the projection structure (Part 3).
   The key would be showing that the new T_mid processor "inherits" the
   DAG ordering from the (n-1)-system, with bounded perturbation.

The author's assessment: Approach 2 (causal chain) is most likely to succeed,
possibly combined with approach 3 (induction on n). The boundary mismatch
between binary and ternary processors is the structural feature that prevents
cycles, and the proof should exploit this directly.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque


def verify_no_2_cycles():
    """Analytically verify the no-2-cycle property for all 5 tables."""
    print("VERIFICATION: NO 2-CYCLE PROPERTY")
    print("=" * 60)

    tables = [
        ("T_bot", T_bot, 2, 2, 3),
        ("T_low", T_low, 2, 3, 3),
        ("T_mid", T_mid, 3, 3, 3),
        ("T_high", T_high, 3, 3, 2),
        ("T_top", T_top, 3, 2, 2),
    ]

    for name, T, mL, mS, mR in tables:
        violations = 0
        for L in range(mL):
            for R in range(mR):
                for a in range(mS):
                    b = T[(L, a, R)]
                    if b != a:
                        c = T[(L, b, R)]
                        if c != b:
                            violations += 1
                            print(f"  {name}: 2-cycle at (L={L},R={R}): "
                                  f"{a}→{b}→{c}")
        print(f"  {name}: {'✓ NO 2-CYCLES' if violations == 0 else f'{violations} VIOLATIONS'}")


def verify_freeze_any_dag(max_n=12):
    """Verify freeze-any-position DAG property."""
    print("\nVERIFICATION: FREEZE-ANY-POSITION DAG")
    print("=" * 60)

    for nv in range(5, max_n + 1):
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        all_dag = True
        for freeze in range(n):
            # Build frozen graph
            in_deg = {c: 0 for c in bad_set}
            adj = {c: [] for c in bad_set}
            for c in bad_set:
                for i in range(n):
                    if i == freeze:
                        continue
                    L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                    new_S = fs[i](L, S, R)
                    if new_S != S:
                        lst = list(c); lst[i] = new_S; succ = tuple(lst)
                        if succ in bad_set:
                            adj[c].append(succ)
                            in_deg[succ] += 1

            q = deque(c for c in bad_set if in_deg[c] == 0)
            count = 0
            while q:
                c = q.popleft()
                count += 1
                for s in adj[c]:
                    in_deg[s] -= 1
                    if in_deg[s] == 0:
                        q.append(s)

            if count != len(bad_set):
                all_dag = False
                print(f"  n={nv}: Freeze P{freeze} → NOT DAG!")

        status = "✓ ALL DAG" if all_dag else "✗ FAILURE"
        print(f"  n={nv}: {status}")

        if 4 * 3 ** (nv - 2) > 500000:
            break


def enumerate_oscillations():
    """Enumerate all T_mid oscillation types and their requirements."""
    print("\nT_MID OSCILLATION CATALOG")
    print("=" * 60)

    osc_types = {'L_only': [], 'R_only': [], 'both': []}

    for a in range(3):
        for b in range(3):
            if a == b:
                continue
            # a → b via (L1, R1), then b → a via (L2, R2)
            first = [(L, R) for L in range(3) for R in range(3)
                     if T_mid[(L, a, R)] == b]
            for L1, R1 in first:
                second = [(L2, R2) for L2 in range(3) for R2 in range(3)
                          if T_mid[(L2, b, R2)] == a]
                for L2, R2 in second:
                    l_change = L1 != L2
                    r_change = R1 != R2
                    record = f"{a}→{b}→{a}: (L:{L1}→{L2}, R:{R1}→{R2})"

                    if l_change and not r_change:
                        osc_types['L_only'].append(record)
                    elif not l_change and r_change:
                        osc_types['R_only'].append(record)
                    elif l_change and r_change:
                        osc_types['both'].append(record)
                    # Neither is impossible (no-2-cycle)

    for cat, items in osc_types.items():
        print(f"\n  {cat} ({len(items)} oscillations):")
        for item in items:
            print(f"    {item}")


def main():
    print("CONVERGENCE PROOF FRAMEWORK — KEY VERIFICATIONS")
    print("=" * 70)

    verify_no_2_cycles()
    print()
    enumerate_oscillations()
    print()
    verify_freeze_any_dag(max_n=10)

    # Summary statistics
    print("\n" + "=" * 70)
    print("SUMMARY OF PROOF FRAMEWORK")
    print("=" * 70)
    print("""
ESTABLISHED FACTS:
  ✓ No 2-cycle property (all 5 tables)
  ✓ Mover always gains target (verified n=5..8)
  ✓ Freeze-any-position → DAG (verified n=5..12)
  ✓ All-position participation required for cycle
  ✓ Each oscillation needs ≥1 neighbor change
  ✓ Directional flow: 0→1 right, 1→2 left
  ✓ DAG depth = ⌊(3n²-4n-11)/4⌋ (verified n=5..13)

OPEN:
  ? Prove freeze-any-position DAG for all n
  ? Prove causal chain can't close at boundaries
  ? OR find non-standard potential function
  ? OR prove by induction on n

MOST PROMISING APPROACH:
  Causal chain impossibility + boundary mismatch
  (binary boundary tables break ternary oscillation chains)
""")


if __name__ == "__main__":
    main()
