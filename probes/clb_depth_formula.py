#!/usr/bin/env python3
"""clb_depth_formula.py — Verify closed-form formula for convergence depth."""

import math

# Data from convergence analysis
data = [
    (5, 11, 5.45, 5, 4, 1.28),
    (6, 18, 8.75, 9, 6, 1.69),
    (7, 27, 13.33, 13, 7, 2.16),
    (8, 37, 18.83, 19, 8, 2.69),
    (9, 49, 25.28, 26, 9, 3.29),
    (10, 62, 32.58, 34, 10, 3.93),
    (11, 77, 40.67, 42, 12, 4.60),
    (12, 93, 49.48, 50, 14, 5.31),
    (13, 111, 59.02, 59, 16, 6.04),
]

print("=== Max Depth Formula Check ===")
print(f"{'n':>3} {'actual':>8} {'floor((3n²-4n-11)/4)':>22} {'match':>6}")
for n, max_d, avg_d, med, best_max, best_avg in data:
    pred = math.floor((3*n*n - 4*n - 11) / 4)
    match = "YES" if pred == max_d else "NO"
    print(f"{n:>3} {max_d:>8} {pred:>22} {match:>6}")

print("\n=== Depth Differences (max_depth(n+1) - max_depth(n)) ===")
for i in range(len(data) - 1):
    n, md = data[i][0], data[i][1]
    n2, md2 = data[i+1][0], data[i+1][1]
    diff = md2 - md
    # Predicted difference: (3(n+1)²-4(n+1)-11)/4 - (3n²-4n-11)/4
    # = (6n+3-4)/4 = (6n-1)/4
    pred_diff = (6*n - 1) / 4
    print(f"  n={n}→{n2}: Δ={diff}, pred=(6n-1)/4={pred_diff:.2f}")

print("\n=== Best-Case Max Depth Pattern ===")
for n, max_d, avg_d, med, best_max, best_avg in data:
    ratio = best_max / n
    print(f"  n={n}: best_max={best_max}, n-1={n-1}, "
          f"ratio={ratio:.2f}")

print("\n=== Hardest Config Pattern ===")
print("  Odd n: (10)^((n-1)/2) 1  — alternating 1,0,1,0,...,1")
print("  Even n: 00(10)^((n-2)/2)  — 0,0,1,0,1,...,0  (and 00...020)")
print()
print("  n=5:  12101 or 10101  (depth 11)")
print("  n=6:  001010, 001020  (depth 18)")
print("  n=7:  1010101          (depth 27)")
print("  n=8:  00101010, 00101020 (depth 37)")
print("  n=9:  101010101        (depth 49)")
print("  n=10: 0010101010, 0010101020 (depth 62)")
print("  n=11: 10101010101      (depth 77)")
print("  n=12: 001010101010, 001010101020 (depth 93)")
print("  n=13: 1010101010101    (depth 111)")

print("\n=== Average Depth Formula Check ===")
# avg_depth looks roughly linear in n but let's check quadratic
# Try avg ≈ an² + bn + c
# n=5: 25a + 5b + c = 5.45
# n=9: 81a + 9b + c = 25.28
# n=13: 169a + 13b + c = 59.02
# From 1&2: 56a + 4b = 19.83 → 14a + b = 4.9575
# From 2&3: 88a + 4b = 33.74 → 22a + b = 8.435
# 8a = 3.4775 → a = 0.4347
# b = 4.9575 - 14*0.4347 = 4.9575 - 6.086 = -1.128
# c = 5.45 - 25*0.4347 - 5*(-1.128) = 5.45 - 10.87 + 5.64 = 0.22
print(f"{'n':>3} {'actual':>8} {'0.435n²-1.13n+0.22':>20}")
for n, max_d, avg_d, med, best_max, best_avg in data:
    pred = 0.4347*n*n - 1.128*n + 0.22
    print(f"{n:>3} {avg_d:>8.2f} {pred:>20.2f}")

print("\n=== Potential Function Violation Rates ===")
pf_data = [
    (5, 32.9, 56.4, 34.2),
    (6, 40.2, 74.0, 43.2),
    (7, 44.3, 84.8, 48.3),
    (8, 46.3, 91.1, 51.1),
    (9, 47.2, 94.8, 52.5),
    (10, 47.5, 96.8, 53.1),
    (11, 47.6, 98.0, 53.4),
    (12, 47.5, 98.7, 53.6),
    (13, 47.5, 99.2, 53.6),
]
print(f"{'n':>3} {'sum%':>8} {'max%':>8} {'hamming%':>10}")
for n, s, m, h in pf_data:
    print(f"{n:>3} {s:>8.1f} {m:>8.1f} {h:>10.1f}")
print("\nNote: 'max' approaches 100% — it is NOT a valid potential function.")
print("'sum' stabilizes near 47.5% — also not a potential function.")
print("None of these simple functions decrease monotonically on bad transitions.")
