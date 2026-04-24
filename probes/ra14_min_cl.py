#!/usr/bin/env python3
"""ra14_min_cl.py — Find minimum CL for valid OW walks, fast version."""
import math
from itertools import combinations


def solve_unique(n, f):
    """Solve c[(p-1)%n] + c[p] = f[p] for all p. Return c or None."""
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
        # Free variable case (n even)
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
        return [A[k] + S[k] * c0 for k in range(n)]


def has_valid_walk(n, fc, winding):
    """Check if valid +-1 cyclic walk with given winding exists."""
    f = [fc[p] - winding for p in range(n)]
    c = solve_unique(n, f)
    if c is None:
        return False
    # Check c_CCW >= 0 and e_CW = c + winding >= 0
    if any(cc < 0 for cc in c):
        return False
    if any(cc + winding < 0 for cc in c):
        return False
    return True


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


for n in [5, 7, 9, 11, 13, 15, 17, 19, 21]:
    threshold = 4 * (3 ** (n - 2))
    min_cl = 999

    # Only need to check one ms placement (by symmetry, all give same min CL)
    # Actually different placements may give different results. Check a few.
    found = False
    for bins in combinations(range(n), 3):
        bins_set = set(bins)
        ms = [2 if p in bins_set else 3 for p in range(n)]
        if not has_no_triple(ms, n):
            continue
        prod = 1
        for m in ms:
            prod *= m
        if prod >= threshold:
            continue

        # Try small CL values
        ternary_pos = [p for p in range(n) if ms[p] == 3]
        binary_pos = [p for p in range(n) if ms[p] == 2]

        # Strategy: try incrementing different procs
        # Binary: +2 per increment. Ternary: +3 per increment.
        # Start from minimum fc = ms. CL_min = 3(n-1).
        # Try adding +2 (binary) and +3 (ternary) increments.
        # CL = 3(n-1) + 2*a + 3*b where a = total binary increments, b = total ternary.
        # Need CL + n even: (3(n-1) + 2a + 3b + n) even = (4n-3+2a+3b) even = (3b+1) even.
        # So 3b ≡ 1 (mod 2) => b odd.

        for total_increment in range(1, 30):
            for b in range(total_increment + 1):
                a = total_increment - b
                if b % 2 == 0:  # need b odd
                    continue
                cl = 3*(n-1) + 2*a + 3*b
                if cl >= min_cl:
                    continue
                if (cl + n) % 2 != 0:
                    continue

                # Try distributing increments
                # Simplest: put all binary incr on first binary, all ternary on first ternary
                fc = list(ms)
                if a > 0:
                    fc[binary_pos[0]] += 2 * a
                # Distribute b ternary increments: try putting on different ternaries
                # Must put odd number of increments total (b is odd)
                # Simplest: put b increments on one ternary
                fc_t = list(fc)
                fc_t[ternary_pos[0]] += 3 * b
                for w in [1, -1]:
                    if has_valid_walk(n, fc_t, w):
                        min_cl = min(min_cl, cl)
                        found = True
                        break

                # Also try distributing on multiple ternaries
                if len(ternary_pos) >= 3 and b >= 3:
                    fc_t2 = list(fc)
                    # Put 1 increment on each of 3 ternaries (if b >= 3)
                    remaining = b
                    idx = 0
                    for tp in ternary_pos[:b]:
                        fc_t2[tp] += 3
                    for w in [1, -1]:
                        if has_valid_walk(n, fc_t2, w):
                            min_cl = min(min_cl, cl)
                            found = True
                            break

        if found:
            break

    if min_cl < 999:
        print(f"n={n}: min CL = {min_cl}, CL > 18: {min_cl > 18}, formula: 2*{(min_cl-n)//2} + {n}")
    else:
        print(f"n={n}: no valid walks found")
