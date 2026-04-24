#!/usr/bin/env python3
"""Recheck: are the 'valid walks' from earlier actually valid?"""
import math
from itertools import combinations


def solve_edge_counts(n, fc, winding=1):
    delta = winding
    f = [fc[p] - delta for p in range(n)]
    A = [0] * n
    S = [0] * n
    A[0] = 0
    S[0] = 1
    for k in range(1, n):
        A[k] = f[k] - A[k-1]
        S[k] = -S[k-1]
    coeff = S[n-1] + 1
    rhs = f[0] - A[n-1]
    if coeff == 0:
        if rhs != 0:
            return None
        lower = float('-inf')
        upper = float('inf')
        for k in range(n):
            if S[k] > 0:
                lower = max(lower, -A[k] / S[k])
            elif S[k] < 0:
                upper = min(upper, -A[k] / S[k])
            else:
                if A[k] < 0:
                    return None
        if lower > upper:
            return None
        c0 = max(math.ceil(lower), 0)
        if c0 > upper:
            return None
        return [A[k] + S[k] * c0 for k in range(n)]
    else:
        if rhs % coeff != 0:
            return None
        c0 = rhs // coeff
        c = [A[k] + S[k] * c0 for k in range(n)]
        if any(cc < 0 for cc in c):
            return None
        return c


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


# Reproduce the earlier "WALK EXISTS" case
n = 7
ms = [2, 2, 3, 3, 2, 3, 3]
fc = [2, 2, 6, 3, 2, 3, 3]
print(f"ms={ms}, fc={fc}")
c = solve_edge_counts(n, fc, winding=-1)
print(f"c_CCW = {c}")
if c:
    e_cw = [c[p] - 1 for p in range(n)]  # winding = -1
    print(f"e_CW = {e_cw}")
    print(f"Any negative e_CW? {any(e < 0 for e in e_cw)}")
    print(f"Any negative c_CCW? {any(cc < 0 for cc in c)}")

    # Verify flow: fc[p] = arrivals = e_CW(p-1) + c_CCW(p)
    for p in range(n):
        arrivals = e_cw[(p-1)%n] + c[p]
        print(f"  p={p}: fc={fc[p]}, arrivals = e_CW({(p-1)%n}) + c_CCW({p}) = {e_cw[(p-1)%n]} + {c[p]} = {arrivals}")

print()
print("The earlier solve_edge_counts only checked c >= 0, NOT e_CW >= 0!")
print("So the 'valid walks' had negative CW edge counts, which are invalid.")
print()
print("Checking: for n=7..13, with single ternary increment, winding +-1:")
print("are there ANY valid solutions with BOTH c_CCW >= 0 AND e_CW >= 0?")
print()

for n in [5, 7, 9, 11, 13, 15, 17, 19, 21]:
    found = 0
    for bins in combinations(range(n), 3):
        if found > 0:
            break
        bins_set = set(bins)
        ms = [2 if p in bins_set else 3 for p in range(n)]
        if not has_no_triple(ms, n):
            continue
        threshold = 4 * (3 ** (n - 2))
        prod = 1
        for m in ms:
            prod *= m
        if prod >= threshold:
            continue

        ternary_pos = [p for p in range(n) if ms[p] == 3]
        for tp in ternary_pos:
            fc = list(ms)
            fc[tp] = 6
            cl = sum(fc)
            if (cl + n) % 2 != 0:
                continue

            for w in [1, -1]:
                c = solve_edge_counts(n, fc, winding=w)
                if c is None:
                    continue
                e_cw = [c[p] + w for p in range(n)]
                if all(cc >= 0 for cc in c) and all(e >= 0 for e in e_cw):
                    found += 1
                    print(f"  n={n}: VALID! ms={ms}, fc={fc}, w={w}")
                    break
            if found > 0:
                break

    if found == 0:
        print(f"  n={n}: NO valid solutions found")

# Now: what about LARGER increments?
# e.g., one ternary at 3x (fc = 9), or multiple ternaries doubled.
print()
print("Trying larger increments:")
for n in [5, 7, 9]:
    threshold = 4 * (3 ** (n - 2))
    found_any = False
    for bins in combinations(range(n), 3):
        if found_any:
            break
        bins_set = set(bins)
        ms = [2 if p in bins_set else 3 for p in range(n)]
        if not has_no_triple(ms, n):
            continue
        prod = 1
        for m in ms:
            prod *= m
        if prod >= threshold:
            continue

        ternary_pos = [p for p in range(n) if ms[p] == 3]
        binary_pos = [p for p in range(n) if ms[p] == 2]

        # Try k_p from 1 to 4 for each ternary, 1 to 3 for binary
        # But this is exponential. Let me try specific patterns.

        # Pattern 1: one ternary at 3x (k=3, fc=9)
        for tp in ternary_pos:
            fc = list(ms)
            fc[tp] = 9
            cl = sum(fc)
            if (cl + n) % 2 != 0:
                continue
            for w in [1, -1]:
                c = solve_edge_counts(n, fc, winding=w)
                if c is None:
                    continue
                e_cw = [c[p] + w for p in range(n)]
                if all(cc >= 0 for cc in c) and all(e >= 0 for e in e_cw):
                    found_any = True
                    print(f"  n={n}: VALID (3x)! ms={ms}, fc={fc}, w={w}")
                    break
            if found_any:
                break

        # Pattern 2: one binary at 2x (fc=4)
        if not found_any:
            for bp in binary_pos:
                fc = list(ms)
                fc[bp] = 4
                # Also need to fix parity: one ternary increment
                for tp in ternary_pos:
                    fc2 = list(fc)
                    fc2[tp] = 6
                    cl = sum(fc2)
                    if (cl + n) % 2 != 0:
                        continue
                    for w in [1, -1]:
                        c = solve_edge_counts(n, fc2, winding=w)
                        if c is None:
                            continue
                        e_cw = [c[p] + w for p in range(n)]
                        if all(cc >= 0 for cc in c) and all(e >= 0 for e in e_cw):
                            found_any = True
                            print(f"  n={n}: VALID (bin+tern)! ms={ms}, fc={fc2}, w={w}")
                            break
                    if found_any:
                        break
                if found_any:
                    break

    if not found_any:
        print(f"  n={n}: No valid solutions with larger increments")
