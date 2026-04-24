"""For the violation configs, check ALL cycling sites.
If a violation config has a cycling site with k <= n-6, we can use that instead."""

n = 10

def has_nocopy(c, n):
    for j in range(4, n-3):
        if c[j] == c[j-1] or c[j] == c[j+1]:
            return False
    return True

# Violation example
c = (0, 0, 0, 0, 1, 2, 0, 2, 0, 0)
print(f"Config: {c}")
print(f"noDeepCopyPair: {has_nocopy(c, n)}")

# Find ALL cycling sites (5 <= k, k+5 <= n, c(k-1) != c(k+1))
for k in range(5, n-4):
    if c[k-1] != c[k+1]:
        print(f"  Cycling site at k={k}: c({k-1})={c[k-1]}, c({k+1})={c[k+1]}, k<= n-6={k <= n-6}")

print()
# Check all 80 violations
violations = []
for c0 in range(2):
    for c1 in range(3):
        for c2 in range(3):
            for c3 in range(3):
                for c7 in range(3):
                    for c8 in range(3):
                        for c9 in range(2):
                            for start in range(3):
                                c = [c0, c1, c2, c3, 0, 0, 0, c7, c8, c9]
                                for j in range(4, 7):
                                    c[j] = (start + j) % 3
                                c = tuple(c)
                                if not has_nocopy(c, n): continue
                                # Check cycling at k=5 (n-5)
                                if c[4] == c[6]: continue
                                violations.append(c)

print(f"Total no-copy configs with cycling at k=5: {len(violations)}")

# For each, check if there's a cycling site with k <= 4 (n-6)
has_better = 0
for c in violations:
    found = False
    for k in range(5, n-4):
        if k <= n - 6 and c[k-1] != c[k+1]:
            found = True
            break
    if found:
        has_better += 1

print(f"Of these, {has_better} have a cycling site with k <= n-6")
print(f"Remaining with ONLY k=n-5: {len(violations) - has_better}")

# Check: for k <= n-6 case, does seam pruning hold?
# n=10, k <= 4 means k can only be 5 (from 5 <= k). But n-6=4, so k <= 4 is impossible with 5 <= k.
# So for n=10: ALL cycling sites have k = 5 = n-5. There's NO k <= n-6.
print(f"\nFor n=10: valid k range is [5, {n-4-1}]. n-6={n-6}. k <= n-6 means k <= {n-6}.")
print(f"Since k >= 5 and k <= {n-6}: {'possible' if 5 <= n-6 else 'IMPOSSIBLE'}")
print("For n=10: k = 5 is the ONLY valid cycling site. The edge case IS the only case.")
print()

# Check n=11
n = 11
print(f"For n={n}: valid k range is [5, {n-4-1}]. n-6={n-6}. k <= n-6 means k <= {n-6}.")
print(f"k=5 is far (k <= n-6={n-6}). k=6=n-5 is edge.")
