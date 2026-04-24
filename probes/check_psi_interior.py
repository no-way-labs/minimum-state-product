"""Check whether Ψ (syntactic potential) is non-increasing on interior copy-neighbor moves."""

# wMid table from SyntheticPotential.lean
wMid = {}
data = [
    (0,0,0,-5), (0,0,1,5), (0,0,2,3),
    (0,1,0,5), (0,1,1,-3), (0,1,2,-5),
    (0,2,0,-3), (0,2,1,5),
    (1,0,0,-5), (1,0,1,5), (1,0,2,1),
    (1,1,0,5), (1,1,1,-3), (1,1,2,-5),
    (1,2,0,-3), (1,2,1,5),
    (2,0,0,-5), (2,0,1,5), (2,0,2,5),
    (2,1,0,5), (2,1,1,-3), (2,1,2,-5),
    (2,2,0,-5), (2,2,1,3), (2,2,2,-2),
]
for L, S, R, v in data:
    wMid[(L, S, R)] = v
# Default 0 for unlisted
for L in range(3):
    for S in range(3):
        for R in range(3):
            if (L, S, R) not in wMid:
                wMid[(L, S, R)] = 0

# For an interior copy-neighbor move at position i (all 5 surrounding positions are Mid):
# Context: (a, b, c_val, d, e) = (c[i-2], c[i-1], c[i], c[i+1], c[i+2])
# Privileged: c_val != b AND c_val != d (for ternary)
# Actually: privileged means c[i] != f(c[i-1], c[i], c[i+1]).
# For CUP-2 at interior, the privileged condition and output depend on the specific rule.
# But the copy-neighbor property means output is either c[i-1] or c[i+1].

# Copy-left: c'[i] = b (= c[i-1]), requires c_val != b (otherwise not a change)
# Copy-right: c'[i] = d (= c[i+1]), requires c_val != d (otherwise not a change)

max_increase = -float('inf')
worst_case = None
increases = []

for a in range(3):
    for b in range(3):
        for c_val in range(3):
            for d in range(3):
                for e in range(3):
                    # Copy-left: c'[i] = b
                    if c_val != b:
                        delta = (
                            (wMid[(a, b, b)] - wMid[(a, b, c_val)]) +
                            (wMid[(b, b, d)] - wMid[(b, c_val, d)]) +
                            (wMid[(b, d, e)] - wMid[(c_val, d, e)])
                        )
                        if delta > max_increase:
                            max_increase = delta
                            worst_case = ('copy-left', a, b, c_val, d, e, delta)
                        if delta > 0:
                            increases.append(('copy-left', a, b, c_val, d, e, delta))

                    # Copy-right: c'[i] = d
                    if c_val != d:
                        delta = (
                            (wMid[(a, b, d)] - wMid[(a, b, c_val)]) +
                            (wMid[(b, d, d)] - wMid[(b, c_val, d)]) +
                            (wMid[(d, d, e)] - wMid[(c_val, d, e)])
                        )
                        if delta > max_increase:
                            max_increase = delta
                            worst_case = ('copy-right', a, b, c_val, d, e, delta)
                        if delta > 0:
                            increases.append(('copy-right', a, b, c_val, d, e, delta))

print(f"Max ΔΨ over all interior copy-neighbor moves: {max_increase}")
print(f"Worst case: {worst_case}")
print(f"Number of cases with ΔΨ > 0: {len(increases)}")
if increases:
    print("\nAll increasing cases:")
    for case in sorted(increases, key=lambda x: -x[-1]):
        print(f"  {case}")
else:
    print("\nΨ is NON-INCREASING for all interior copy-neighbor moves!")
