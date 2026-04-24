#!/usr/bin/env python3
"""
Quick check: does sub-threshold + ≥3 binary + no 3 consecutive force
alternating [2,3,2,3,...] layout?

Sub-threshold means product < 4·3^(n-2).
With all m ∈ {2,3}: product = 2^b * 3^(n-b) where b = binary count.
Sub-threshold: 2^b * 3^(n-b) < 4 * 3^(n-2) = 4/9 * 3^n
So 2^b * 3^(n-b) < 4/9 * 3^n
(2/3)^b * 3^n < 4/9 * 3^n
(2/3)^b < 4/9
b * log(2/3) < log(4/9)
b > log(4/9) / log(2/3) = log(9/4) / log(3/2)

log(9/4) / log(3/2) = ln(2.25) / ln(1.5) = 0.8109 / 0.4055 ≈ 2.0

So b > 2, i.e., b ≥ 3. Which we have (≥3 binary).

But does this force ALTERNATING? No — [2,2,3,2,3,3,...] also has ≥3 binary
with product 2^3 * 3^(n-3) < 4 * 3^(n-2) since 8 < 12.

Wait: 2^3 * 3^(n-3) vs 4 * 3^(n-2) = 2^2 * 3^(n-2)
8 * 3^(n-3) vs 4 * 3^(n-2) = 4 * 3 * 3^(n-3) = 12 * 3^(n-3)
8 < 12 ✓

So [2,2,3,2,3,3,...,3] IS sub-threshold with ≥3 binary but NOT alternating
(has 2 consecutive binary at start).

But we have "no 3 consecutive binary." Can we have 2 consecutive?
Yes: [2,2,3,2,3,...] has b=3, no 3 consecutive, but is not alternating.

So non-alternating IS reachable. The sorry cannot be eliminated by structure alone.

However: with 2 consecutive binary (but not 3), we're in a DIFFERENT
case from pure alternating. The non-consecutive sorry specifically says
"no three consecutive binary" — it allows 2 consecutive.

What about m ≥ 4? Sub-threshold forces product < 4·3^(n-2).
If any proc has m ≥ 4: product ≥ 4 * 2^(b-1) * 3^(n-b-1) ... hmm complex.
Let's just check: with n=9, product < 4*3^7 = 8748.
All m∈{2,3}: product = 2^b * 3^(9-b). For b=3: 8*729 = 5832 < 8748 ✓
With one m=4: min product with 3 binary + 1 quaternary + rest ternary:
2^3 * 4 * 3^5 = 8*4*243 = 7776 < 8748 ✓. So m=4 IS possible sub-threshold.

So non-alternating includes both "2 consecutive binary" and "has quaternary."
"""
import math

# Check if non-alternating is possible under sub-threshold
for n in [9, 10, 11]:
    threshold = 4 * 3**(n-2)
    print(f"n={n}, threshold={threshold}")

    # Check 2-consecutive binary
    for b in range(3, n):
        prod = 2**b * 3**(n-b)
        if prod < threshold:
            print(f"  b={b}: 2^{b}*3^{n-b} = {prod} < {threshold} ✓ (possible non-alternating)")

    # Check with quaternary
    prod_q = 2**3 * 4 * 3**(n-4)
    print(f"  With quaternary: 2^3*4*3^{n-4} = {prod_q} {'<' if prod_q < threshold else '>='} {threshold}")

print("\nConclusion: non-alternating IS reachable under sub-threshold.")
print("The non-alternating sorry cannot be eliminated by structure alone.")
print("It needs its own EC argument (possibly similar to consecutive-binary).")
