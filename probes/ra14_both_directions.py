#!/usr/bin/env python3
"""Check BOTH winding directions more carefully."""
from itertools import combinations
import math


def solve_edge_counts_all(n, fc, winding=1):
    """Return ALL valid c_ccw solutions (if free variable exists)."""
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

    results = []
    if coeff == 0:
        if rhs != 0:
            return []
        lower = float('-inf')
        upper = float('inf')
        for k in range(n):
            if S[k] > 0:
                lower = max(lower, -A[k] / S[k])
            elif S[k] < 0:
                upper = min(upper, -A[k] / S[k])
            else:
                if A[k] < 0:
                    return []
        if lower > upper:
            return []
        c0_min = max(math.ceil(lower), 0)
        c0_max = int(upper)
        for c0 in range(c0_min, c0_max + 1):
            c = [A[k] + S[k] * c0 for k in range(n)]
            e_cw = [c[p] + winding for p in range(n)]
            if all(cc >= 0 for cc in c) and all(e >= 0 for e in e_cw):
                results.append((c, e_cw))
    else:
        if rhs % coeff != 0:
            return []
        c0 = rhs // coeff
        c = [A[k] + S[k] * c0 for k in range(n)]
        e_cw = [c[p] + winding for p in range(n)]
        if all(cc >= 0 for cc in c) and all(e >= 0 for e in e_cw):
            results.append((c, e_cw))
    return results


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


print("COMPLETE edge count search for BOTH winding directions")
print("=" * 70)

for n in [5, 7, 9, 11]:
    threshold = 4 * (3 ** (n - 2))
    print(f"\nn={n}, threshold={threshold}")

    total_valid = 0
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

        ternary_pos = [p for p in range(n) if ms[p] == 3]

        # Try all single-ternary increments
        for tp in ternary_pos:
            fc = list(ms)
            fc[tp] = 6
            cl = sum(fc)
            if (cl + n) % 2 != 0:
                continue

            for w in [1, -1]:
                solutions = solve_edge_counts_all(n, fc, winding=w)
                for c, e_cw in solutions:
                    total_valid += 1
                    if n <= 9:
                        print(f"  VALID: ms={ms}, fc={fc}, w={w}")
                        print(f"    c_CCW={c}, e_CW={e_cw}")
                        print(f"    Total edges per ring edge: {[c[p]+e_cw[p] for p in range(n)]}")

        # Try all triple-ternary increments (3 ternaries doubled)
        if len(ternary_pos) >= 3:
            for i in range(len(ternary_pos)):
                for j in range(i+1, len(ternary_pos)):
                    for k in range(j+1, len(ternary_pos)):
                        fc = list(ms)
                        fc[ternary_pos[i]] = 6
                        fc[ternary_pos[j]] = 6
                        fc[ternary_pos[k]] = 6
                        cl = sum(fc)
                        if (cl + n) % 2 != 0:
                            continue

                        for w in [1, -1]:
                            solutions = solve_edge_counts_all(n, fc, winding=w)
                            for c_sol, e_cw_sol in solutions:
                                total_valid += 1
                                if n <= 7:
                                    print(f"  VALID (3x): ms={ms}, fc={fc}, w={w}")
                                    print(f"    c_CCW={c_sol}, e_CW={e_cw_sol}")

        # Try single binary increment (fc from 2 to 4)
        binary_pos = [p for p in range(n) if ms[p] == 2]
        for bp in binary_pos:
            fc = list(ms)
            fc[bp] = 4
            cl = sum(fc)
            if (cl + n) % 2 != 0:
                continue

            for w in [1, -1]:
                solutions = solve_edge_counts_all(n, fc, winding=w)
                for c_sol, e_cw_sol in solutions:
                    total_valid += 1
                    if n <= 9:
                        print(f"  VALID (bin++): ms={ms}, fc={fc}, w={w}")
                        print(f"    c_CCW={c_sol}, e_CW={e_cw_sol}")

    print(f"  Total valid edge count solutions: {total_valid}")
