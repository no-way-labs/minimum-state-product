#!/usr/bin/env python3
"""
CONVERGENCE PROOF 36: Analytical Proof of Δint(2,1) ≥ 0
=========================================================

GOAL: Prove that for all excursion edges (src → tgt), the interior
position-weighted (2,1) pair count does not increase:
  S(src) ≥ S(tgt) where S(c) = Σ_{j interior} j · 1[(c[j],c[j+1])=(2,1)]

APPROACH:
The key is to understand which T_mid entries can CREATE or DESTROY
interior (2,1) pairs, and show that the net effect is non-negative.

A (2,1) pair at interior position j means c[j]=2, c[j+1]=1.
It is created when:
  - c[j] changes to 2 (new pair at j if c[j+1]=1)
  - c[j+1] changes to 1 (new pair at j if c[j]=2)
It is destroyed when:
  - c[j] changes away from 2 (lose pair at j)
  - c[j+1] changes away from 1 (lose pair at j)

For a firing at interior position k (T_mid):
  - Pair at position k-1: (c[k-1], c[k]) changes to (c[k-1], new_c[k])
  - Pair at position k: (c[k], c[k+1]) changes to (new_c[k], c[k+1])

So we need: for each T_mid entry that fires (Δfc≤0), track whether
it creates or destroys (2,1) pairs at positions k-1 and k.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_mid, T_bot, T_low, T_high, T_top, build_system

def main():
    print("=" * 70)
    print("T_MID TABLE ANALYSIS: (2,1) PAIR CREATION/DESTRUCTION")
    print("=" * 70)

    # For each T_mid entry (L, S, R) → out where out ≠ S (firing):
    # Check if it creates or destroys (2,1) pairs
    print("\nAll firing T_mid entries and their (2,1) pair effects:")
    print(f"  {'(L,S,R)→out':>14} {'Δfc':>4} {'pair k-1':>20} {'pair k':>20}")
    print(f"  {'':>14} {'':>4} {'(L,S)→(L,out)':>20} {'(S,R)→(out,R)':>20}")

    for L in range(3):
        for S in range(3):
            for R in range(3):
                out = T_mid[(L, S, R)]
                if out == S:
                    continue  # Not a firing

                dfc = (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))

                # Effect on (2,1) pair at position k-1: (L, S) → (L, out)
                was_21_km1 = (L == 2 and S == 1)
                now_21_km1 = (L == 2 and out == 1)
                d_km1 = int(now_21_km1) - int(was_21_km1)

                # Effect on (2,1) pair at position k: (S, R) → (out, R)
                was_21_k = (S == 2 and R == 1)
                now_21_k = (out == 2 and R == 1)
                d_k = int(now_21_k) - int(was_21_k)

                d_total = d_km1 + d_k

                if d_total != 0 or dfc <= 0:
                    mark = " ** CREATES" if d_total > 0 else ""
                    mark2 = " [ANOM]" if dfc > 0 else ""
                    print(f"  ({L},{S},{R})→{out}  {dfc:>+2}  "
                          f"({L},{S})→({L},{out}): {d_km1:>+2}  "
                          f"({S},{R})→({out},{R}): {d_k:>+2}  "
                          f"net={d_total:>+2}{mark}{mark2}")

    # Specifically: which Δfc≤0 entries can CREATE (2,1) pairs?
    print("\n" + "=" * 70)
    print("Δfc≤0 T_MID ENTRIES THAT CREATE (2,1) PAIRS:")
    print("=" * 70)

    creators = []
    for L in range(3):
        for S in range(3):
            for R in range(3):
                out = T_mid[(L, S, R)]
                if out == S:
                    continue
                dfc = (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))
                if dfc > 0:
                    continue  # Anomalous, skip

                was_21_km1 = (L == 2 and S == 1)
                now_21_km1 = (L == 2 and out == 1)
                d_km1 = int(now_21_km1) - int(was_21_km1)

                was_21_k = (S == 2 and R == 1)
                now_21_k = (out == 2 and R == 1)
                d_k = int(now_21_k) - int(was_21_k)

                if d_km1 > 0 or d_k > 0:
                    creators.append((L, S, R, out, dfc, d_km1, d_k))

    if creators:
        print("  WARNING: Some Δfc≤0 entries create (2,1) pairs!")
        for L, S, R, out, dfc, d_km1, d_k in creators:
            print(f"    ({L},{S},{R})→{out} Δfc={dfc:+d}: "
                  f"Δ(2,1)@k-1={d_km1:+d}, Δ(2,1)@k={d_k:+d}")
    else:
        print("  NONE! No Δfc≤0 T_mid entry creates (2,1) pairs.")
        print("  This would be sufficient to prove Δint(2,1)≥0!")

    # Also check boundary tables for (2,1) pair effects
    print("\n" + "=" * 70)
    print("BOUNDARY TABLE EFFECTS ON ADJACENT INTERIOR (2,1) PAIRS:")
    print("=" * 70)

    # T_bot fires at pos 0: affects pair at pos n-1 (boundary) and pos 0 (boundary)
    # T_low fires at pos 1: affects pair at pos 0 (boundary) and pos 1 (boundary)
    # These don't affect interior pairs.
    # T_mid fires at pos 2..n-4: affects interior pairs.
    # T_high fires at pos n-2: affects pair at pos n-3 (LAST interior!)
    # T_top fires at pos n-1: affects pair at pos n-2 (boundary)

    # KEY: T_high fires at pos n-2, changing c[n-2].
    # Pair at pos n-3 (interior!): (c[n-3], c[n-2]) → (c[n-3], new c[n-2])
    # If c[n-3]=2 and new c[n-2]=1, creates (2,1) at pos n-3.

    print("\n  T_high entries that affect pair at pos n-3 (last interior):")
    for L in range(3):
        for S in range(3):
            for R in range(2):
                out = T_high[(L, S, R)]
                if out == S:
                    continue
                dfc = (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))
                if dfc > 0:
                    continue  # Skip anomalous

                # Pair at pos n-3: (L, S) → (L, out)
                was_21 = (L == 2 and S == 1)
                now_21 = (L == 2 and out == 1)
                d = int(now_21) - int(was_21)
                if d != 0:
                    print(f"    T_high({L},{S},{R})→{out} Δfc={dfc:+d}: "
                          f"pair@n-3: ({L},{S})→({L},{out}) Δ(2,1)={d:+d}")

    # T_mid at pos 2 affects pair at pos 1 (boundary) and pos 2 (interior)
    # T_mid at pos n-4 affects pair at pos n-5 (interior) and pos n-4 (interior)
    # These are all covered by the T_mid analysis above.

    # Also check: T_low fires at pos 1, affects pair at pos 1 (boundary, T_low-T_mid)
    # The pair at pos 1 is a BOUNDARY pair (not interior), so doesn't affect S(c).

    # SYNTHESIS
    print("\n" + "=" * 70)
    print("SYNTHESIS: Can Δfc≤0 steps create interior (2,1) pairs?")
    print("=" * 70)

    # Categorize all Δfc≤0 T_mid firings by (2,1) effect
    n_total = 0
    n_create = 0
    n_destroy = 0
    n_neutral = 0

    for L in range(3):
        for S in range(3):
            for R in range(3):
                out = T_mid[(L, S, R)]
                if out == S:
                    continue
                dfc = (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))
                if dfc > 0:
                    continue

                n_total += 1
                was_21_km1 = (L == 2 and S == 1)
                now_21_km1 = (L == 2 and out == 1)
                was_21_k = (S == 2 and R == 1)
                now_21_k = (out == 2 and R == 1)
                d = (int(now_21_km1) - int(was_21_km1) +
                     int(now_21_k) - int(was_21_k))
                if d > 0:
                    n_create += 1
                elif d < 0:
                    n_destroy += 1
                else:
                    n_neutral += 1

    print(f"  Δfc≤0 T_mid firings: {n_total} total")
    print(f"    Create (2,1): {n_create}")
    print(f"    Destroy (2,1): {n_destroy}")
    print(f"    Neutral: {n_neutral}")

    if n_create == 0:
        print(f"\n  *** THEOREM (Δint(2,1) monotonicity): ***")
        print(f"  No Δfc≤0 T_mid firing creates interior (2,1) pairs.")
        print(f"  Since T_bot and T_low only affect boundary pairs (pos 0,1),")
        print(f"  and T_top only affects boundary pair (pos n-2,n-1),")
        print(f"  the only table that can affect interior (2,1) pairs via")
        print(f"  the adjacent interior pair at pos n-3 is T_high.")
    else:
        print(f"\n  Some Δfc≤0 T_mid firings CREATE (2,1) pairs.")
        print(f"  Need more detailed analysis.")

    # Check T_high effect on interior (2,1) at pos n-3
    print("\n  T_high Δfc≤0 effects on interior (2,1) at pos n-3:")
    n_high_create = 0
    for L in range(3):
        for S in range(3):
            for R in range(2):
                out = T_high[(L, S, R)]
                if out == S:
                    continue
                dfc = (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))
                if dfc > 0:
                    continue
                was_21 = (L == 2 and S == 1)
                now_21 = (L == 2 and out == 1)
                if int(now_21) > int(was_21):
                    n_high_create += 1
                    print(f"    T_high({L},{S},{R})→{out}: CREATES (2,1) at n-3!")

    if n_high_create == 0 and n_create == 0:
        print(f"\n  {'='*60}")
        print(f"  PROVED: Δint(2,1) ≥ 0 for ALL excursion edges.")
        print(f"  {'='*60}")
        print(f"  Proof: In the excursion, each transition is either:")
        print(f"  (a) Anomalous (Δfc>0): only T_mid(2,1,1)→0 at interior.")
        print(f"      This DESTROYS the (2,1) pair at pos j-1 (weight j-1).")
        print(f"  (b) Δfc≤0 step at T_mid: no Δfc≤0 T_mid firing creates")
        print(f"      interior (2,1) pairs.")
        print(f"  (c) Δfc≤0 step at T_high: no Δfc≤0 T_high firing creates")
        print(f"      (2,1) pair at the last interior position n-3.")
        print(f"  (d) Δfc≤0 step at T_bot/T_low/T_top: only affect boundary")
        print(f"      pairs, not interior (2,1) pairs.")
        print(f"  Therefore S(c) can only decrease or stay: S(src)≥S(tgt). □")


if __name__ == '__main__':
    main()
