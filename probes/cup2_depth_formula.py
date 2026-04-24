#!/usr/bin/env python3
"""Check DAG depth formula from the verification data."""

# Data from cup2_final_verify.py output
data = {
    4: 5,
    5: 10,
    6: 17,
    7: 27,
    8: 39,
    9: 52,
    10: 67,
    11: 83,
    12: 101,
    13: 120,
}

print("DAG depth analysis:")
print(f"{'n':>3} {'depth':>6} {'diff':>5} {'diff2':>5}")
prev_d = None
prev_diff = None
for n in sorted(data):
    d = data[n]
    diff = d - prev_d if prev_d is not None else None
    diff2 = diff - prev_diff if diff is not None and prev_diff is not None else None
    prev_d = d
    prev_diff = diff
    print(f"{n:>3} {d:>6} {str(diff) if diff else '':>5} {str(diff2) if diff2 else '':>5}")

# Second differences look constant? Check polynomial fit
print("\nTesting quadratic: a*n^2 + b*n + c")
# Use n=5,6,7 to solve
# 25a + 5b + c = 10
# 36a + 6b + c = 17
# 49a + 7b + c = 27
# 11a + b = 7
# 13a + b = 10
# 2a = 3 => a = 3/2
# b = 7 - 11*3/2 = 7 - 16.5 = -9.5
# c = 10 - 25*1.5 - 5*(-9.5) = 10 - 37.5 + 47.5 = 20
a, b, c = 1.5, -9.5, 20
print(f"  Candidate: {a}n^2 + {b}n + {c}")
for n in sorted(data):
    pred = a * n**2 + b * n + c
    match = "MATCH" if pred == data[n] else f"OFF by {data[n] - pred}"
    print(f"  n={n}: pred={pred:.0f}, actual={data[n]}, {match}")

# Try (3n^2 - 19n + 40) / 2
print("\nTesting (3n^2 - 19n + 40) / 2:")
for n in sorted(data):
    pred = (3 * n**2 - 19 * n + 40) // 2
    match = "MATCH" if pred == data[n] else f"OFF by {data[n] - pred}"
    print(f"  n={n}: pred={pred}, actual={data[n]}, {match}")

# Good configs formula check
print("\nGood configs formula: (n+2)(n+3)/2 - 5")
for n in range(4, 14):
    g = (n + 2) * (n + 3) // 2 - 5
    alt = n * n // 2 + 3 * n // 2  # simplification
    print(f"  n={n}: (n+2)(n+3)/2-5 = {g},  n^2/2+3n/2 = {(n*n+5*n+6)//2-5}")
