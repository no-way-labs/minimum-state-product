#!/usr/bin/env python3
"""Lattice walk analysis for FR at non-sandwiched ternary.

For ternary t between binary bL (mod 2) and ternary bR (mod m):
- Phase trajectory of (c[bL], c[bR]) in {0,1} x Z_m
- Each bL firing: toggle first coord (T operation)
- Each bR firing: increment second coord (I operation)
- FR holds iff endpoint value appears at some earlier step

Model: path from (0,0) to (J,K) with J toggle-steps and K increment-steps.
FR iff some intermediate point (j,k) with j ≡ J mod 2 AND k ≡ K mod m.

This generalizes Both-Even FR (m=2: J even AND K even → FR).
For m=3: the "return" condition is J even AND K ≡ 0 mod 3.
"""
from itertools import combinations
from collections import Counter
import math

def fr_analysis(J, K, m):
    """Count paths from (0,0) to (J,K) that pass through a G-point.

    G = {(j,k) : j ≡ J mod 2, k ≡ K mod m, (j,k) != (J,K), 0 ≤ j ≤ J, 0 ≤ k ≤ K}.
    Path: sequence of J toggle-steps and K increment-steps.
    """
    total_steps = J + K
    if total_steps == 0:
        return 1, 1  # trivial: start = end = mover

    total_paths = math.comb(total_steps, J)

    # Check if start (0,0) is in G
    start_in_G = (0 % 2 == J % 2) and (0 % m == K % m)
    if start_in_G:
        return total_paths, total_paths  # ALL paths have FR (start = mover value)

    # Enumerate all paths and check FR
    fr_count = 0
    # A path is determined by which of the total_steps positions are toggles
    for toggle_positions in combinations(range(total_steps), J):
        toggle_set = set(toggle_positions)
        # Trace path
        j, k = 0, 0
        has_fr = False
        for step in range(total_steps):
            if step in toggle_set:
                j += 1
            else:
                k += 1
            # Check if current point (j,k) is in G (and not the endpoint)
            if (j, k) != (J, K):
                if j % 2 == J % 2 and k % m == K % m:
                    has_fr = True
                    break
        if has_fr:
            fr_count += 1

    return fr_count, total_paths

print("=" * 70)
print("LATTICE WALK FR ANALYSIS")
print("=" * 70)

# Part 1: Sandwiched ternary (m=2, both binary neighbors)
print("\n--- m=2 (sandwiched: both binary neighbors) ---")
print("G-condition: j ≡ J mod 2 AND k ≡ K mod 2 (Both-Even)")
print(f"{'J':>3} {'K':>3} | {'Paths':>8} {'FR':>8} {'Rate':>8} | Note")
print("-" * 60)

for J in range(6):
    for K in range(6):
        if J + K == 0 or J + K > 8:
            continue
        fr, total = fr_analysis(J, K, 2)
        rate = 100 * fr / total if total > 0 else 0
        note = ""
        if J % 2 == 0 and K % 2 == 0:
            note = "RETURN (start in G)"
        elif rate == 0:
            note = "ALWAYS FAILS"
        elif rate == 100:
            note = "ALWAYS FR"
        print(f"{J:>3} {K:>3} | {total:>8} {fr:>8} {rate:>7.1f}% | {note}")

# Part 2: Non-sandwiched ternary (m=3, one binary + one ternary neighbor)
print("\n\n--- m=3 (non-sandwiched: binary + ternary neighbor) ---")
print("G-condition: j ≡ J mod 2 AND k ≡ K mod 3 (Both-Return)")
print(f"{'J':>3} {'K':>3} | {'Paths':>8} {'FR':>8} {'Rate':>8} | Note")
print("-" * 60)

fr_fail_patterns = []  # (J, K) that can fail FR

for J in range(8):
    for K in range(8):
        if J + K == 0 or J + K > 10:
            continue
        fr, total = fr_analysis(J, K, 3)
        rate = 100 * fr / total if total > 0 else 0
        note = ""
        if J % 2 == 0 and K % 3 == 0:
            note = "RETURN (start in G)"
        elif rate == 0:
            note = "ALWAYS FAILS"
        elif rate == 100:
            note = "ALWAYS FR"
        elif rate < 100:
            note = f"PARTIAL ({total - fr} fail)"
            fr_fail_patterns.append((J, K, fr, total))
        print(f"{J:>3} {K:>3} | {total:>8} {fr:>8} {rate:>7.1f}% | {note}")

# Part 3: Analysis of failure patterns for m=3
print("\n\n--- FAILURE PATTERN ANALYSIS (m=3) ---")
print("Which (J,K) have paths that AVOID all G-points?")

for J, K, fr, total in fr_fail_patterns[:20]:
    print(f"\n  (J={J}, K={K}): {total-fr}/{total} paths fail FR ({100*(total-fr)/total:.1f}%)")
    # List the G-points in [0,J]x[0,K] excluding endpoint
    g_points = [(j,k) for j in range(J+1) for k in range(K+1)
                 if j % 2 == J % 2 and k % 3 == K % 3 and (j,k) != (J,K)]
    print(f"    G-points (excluding endpoint): {g_points}")

# Part 4: KEY — What values of (J,K) can arise at P5?
# P5 phase: J = P4 firings, K = P6 firings
# Constraint: J + K ≤ phase duration - 1 (mover doesn't fire P4 or P6)
# Actually J + K = number of P4/P6 firings. Other procs also fire.
print("\n\n--- KEY QUESTION: CAN FR-FAILING (J,K) ALWAYS BE AVOIDED? ---")
print("\n(J,K) pairs where FR can fail (rate < 100%):")
fail_jk = set()
for J in range(10):
    for K in range(10):
        if J + K == 0 or J + K > 12:
            continue
        fr, total = fr_analysis(J, K, 3)
        if fr < total:
            fail_jk.add((J, K))
            if J + K <= 6:
                print(f"  J={J}, K={K}: {total-fr}/{total} paths fail FR")

# Part 5: m=2 comparison — which (J,K) can fail for sandwiched?
print("\n\n(J,K) pairs where FR can fail for m=2 (sandwiched):")
fail_jk_m2 = set()
for J in range(10):
    for K in range(10):
        if J + K == 0 or J + K > 10:
            continue
        fr, total = fr_analysis(J, K, 2)
        if fr < total:
            fail_jk_m2.add((J, K))
            if J + K <= 6:
                print(f"  J={J}, K={K}: {total-fr}/{total} paths fail FR")

# Part 6: CRITICAL — For m=3, what's the MINIMUM J+K for guaranteed FR?
print("\n\n--- MINIMUM J+K FOR GUARANTEED FR ---")
for m in [2, 3, 4]:
    print(f"\nm={m}:")
    for f in range(1, 15):
        all_fr = True
        for J in range(f + 1):
            K = f - J
            fr, total = fr_analysis(J, K, m)
            if fr < total:
                all_fr = False
                break
        if all_fr:
            print(f"  f=J+K={f}: ALL (J,K) with J+K={f} have 100% FR → guaranteed at f≥{f}")
            break
    else:
        print(f"  No guaranteed threshold found for f ≤ 14")

# Part 7: For m=3, characterize the "anti-diagonal" — (J,K) that ALWAYS fail
print("\n\n--- 'ANTI-DIAGONAL' PATTERNS (m=3): (J,K) where ALL paths fail FR ---")
for J in range(10):
    for K in range(10):
        if J + K == 0 or J + K > 12:
            continue
        fr, total = fr_analysis(J, K, 3)
        if fr == 0 and total > 0:
            # Check: J odd OR K ≢ 0 mod 3, AND no G-point reachable
            g_points = [(j,k) for j in range(J+1) for k in range(K+1)
                         if j % 2 == J % 2 and k % 3 == K % 3 and (j,k) != (J,K)]
            print(f"  J={J}, K={K}: ALL {total} paths fail. G-points: {g_points}")

print("\n\nDone.")
