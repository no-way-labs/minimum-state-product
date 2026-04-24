#!/usr/bin/env python3
"""
ra14_cl_lower_bound.py — Prove CL > 18 for all valid OW walks.

For valid edge counts: e_CW[p] >= 0 and c_CCW[p] >= 0 for all edges p.
e_CW[p] - c_CCW[p] = winding = +-1.
fc[p] = e_CW[(p-1)%n] + c_CCW[p] (arrivals from left + right).
fc[p] = multiple of ms[p].

For winding = +1: e_CW[p] = c_CCW[p] + 1.
fc[p] = (c_CCW[(p-1)%n] + 1) + c_CCW[p] = c_CCW[(p-1)%n] + c_CCW[p] + 1.

So c_CCW[(p-1)%n] + c_CCW[p] = fc[p] - 1.

For binary p (fc = 2k): c_L + c_R = 2k - 1 (odd).
For ternary p (fc = 3k): c_L + c_R = 3k - 1.

CL = sum(fc[p]) = sum(c_L + c_R + 1) = 2*sum(c) + n.
Wait: CL = sum_p fc[p] = sum_p (c[(p-1)%n] + c[p] + 1) = 2*sum(c) + n.
So CL = 2*C + n, where C = sum of all c_CCW values.

For n=5: CL = 2C + 5. Need CL > 18: C >= 7.
For n=7: CL = 2C + 7. Need CL > 18: C >= 6.
For n=9: CL = 2C + 9. Need CL > 18: C >= 5.

CL = 2C + n. Also CL = sum(fc).
C = (CL - n)/2 = (sum(fc) - n)/2.

For minimum fc = ms: CL = 3(n-1). C = (3(n-1) - n)/2 = (2n-3)/2.
For n=5: C = 3.5. NOT INTEGER. This confirms min fc doesn't have valid walks.

For valid walks: CL + n even, so CL = 2C + n requires (2C + n) + n = 2C + 2n even.
Always true. And CL + n = 2C + 2n even. CHECK.

Also CL must satisfy CL ≡ n (mod 2) for winding. Since CL = 2C + n: CL mod 2 = n mod 2. CHECK.

Now: what constraints does the edge count system impose on C?

For each edge p: c_CCW[p] >= 0.
For each edge p: c_CCW[p] + 1 >= 0 (always true).
For each vertex p: c_CCW[(p-1)%n] + c_CCW[p] + 1 = fc[p].
So: c_CCW[(p-1)%n] + c_CCW[p] = fc[p] - 1.

This is a system of n equations in n unknowns on a ring.

For binary p: c_L + c_p = 2k_p - 1. (Left edge + right edge = fc - 1.)
Wait, the indexing: vertex p has left edge = edge (p-1, p), which is edge (p-1).
And right edge = edge (p, p+1), which is edge p.

c_CCW of edge (p-1, p) = c_CCW[(p-1)%n].
c_CCW of edge (p, p+1) = c_CCW[p].

So vertex p: c_CCW[(p-1)%n] + c_CCW[p] = fc[p] - 1.

Sum over all vertices: sum_p (c_CCW[(p-1)%n] + c_CCW[p]) = sum_p (fc[p] - 1).
LHS = 2 * sum(c_CCW) = 2C.
RHS = CL - n.
So 2C = CL - n, confirming CL = 2C + n.

Now: C = sum of c_CCW[p] for all edges p.
Each c_CCW[p] >= 0.
Each pair c_CCW[(p-1)] + c_CCW[p] = fc[p] - 1.

For binary p: c_left + c_right = 2k_p - 1 (odd, >= 1 since k_p >= 1).
For ternary p: c_left + c_right = 3k_p - 1 (>= 2 since k_p >= 1).

With 3 binary and (n-3) ternary:
Sum of all (c_left + c_right) = sum(fc - 1) = CL - n = 2C.
But each c appears in exactly 2 terms (as c_left for vertex p+1 and c_right for vertex p).
So the sum is indeed 2C.

For each binary vertex: c_left + c_right >= 1 (at least 1 CCW traversal on one of its edges).
For each ternary vertex: c_left + c_right >= 2.

MINIMUM C: This is a linear programming problem.
Minimize C = sum(c) subject to:
  c[p] >= 0 for all p
  c[(p-1)%n] + c[p] = fc[p] - 1 for all p

The system is determined (up to parity). For n odd: unique solution given one c value.
For n even: one degree of freedom.

Let me compute the minimum CL analytically.

For n ODD with winding +1:
The system c[(p-1)%n] + c[p] = f[p] where f[p] = fc[p] - 1.
Alternating sum: c[0] - c[1] + c[2] - ... = f[1] - f[2] + f[3] - ...
Actually: from the system:
c[n-1] + c[0] = f[0]
c[0] + c[1] = f[1]
c[1] + c[2] = f[2]
...
c[n-2] + c[n-1] = f[n-1]

Subtracting consecutive equations:
c[0] - c[n-1] = f[1] - f[0]  (from eqs 1,0)
Wait, let me just solve directly.

c[1] = f[1] - c[0]
c[2] = f[2] - c[1] = f[2] - f[1] + c[0]
c[3] = f[3] - c[2] = f[3] - f[2] + f[1] - c[0]
...
c[k] = (-1)^k * c[0] + sum_{j=1}^{k} (-1)^{k-j} * f[j]

For odd n: c[n-1] = (-1)^{n-1} * c[0] + stuff = -c[0] + stuff (since n-1 even, (-1)^{n-1} = -1... wait n odd, n-1 even, (-1)^{n-1} = (-1)^{even} = 1).

Hmm, let me be more careful. For n=5:
c[1] = f[1] - c[0]
c[2] = f[2] - f[1] + c[0]
c[3] = f[3] - f[2] + f[1] - c[0]
c[4] = f[4] - f[3] + f[2] - f[1] + c[0]

Constraint: c[4] + c[0] = f[0].
c[4] + c[0] = f[4] - f[3] + f[2] - f[1] + c[0] + c[0] = f[4] - f[3] + f[2] - f[1] + 2*c[0] = f[0].
So 2*c[0] = f[0] - f[4] + f[3] - f[2] + f[1].
c[0] = (f[0] + f[1] - f[2] + f[3] - f[4]) / 2.

For this to be a non-negative integer: the numerator must be even and non-negative.
Also all c[k] >= 0.

The key constraint is: ALL c[k] >= 0 and ALL e_CW[k] = c[k] + 1 >= 0 (always true).

So we need ALL c[k] >= 0, which constrains the fc values.

For the MINIMUM CL: we want to minimize CL = 2C + n = 2*sum(c) + n.
Subject to all c >= 0 and the ring constraint.

The minimum is when c = 0 everywhere possible.
With c[p] = 0 for all p: fc[p] - 1 = c[(p-1)] + c[p] = 0 + 0 = 0. So fc[p] = 1 for all p.
But fc[p] must be a multiple of ms[p] >= 2. So fc[p] >= 2. fc[p] - 1 >= 1.
Can't have all c = 0.

Minimum C: at each vertex, c_left + c_right >= ms[p] - 1 >= 1.
The minimum C satisfying these constraints.

For 3 binary (ms=2): c_left + c_right >= 1 at binary.
For (n-3) ternary (ms=3): c_left + c_right >= 2 at ternary.
Total: 2C = sum(fc - 1) >= 3*1 + (n-3)*2 = 3 + 2n - 6 = 2n - 3.
C >= (2n-3)/2. For n=5: C >= 3.5, so C >= 4 (integer). CL >= 2*4 + 5 = 13.
For n=7: C >= 5.5, so C >= 6. CL >= 2*6 + 7 = 19.
For n=9: C >= 7.5, so C >= 8. CL >= 2*8 + 9 = 25.

But we also need the PARITY constraint and the ring equations to be satisfiable!
Not every C >= (2n-3)/2 can be achieved with valid c values.

Actually: CL = 2C + n and fc[p] - 1 = c_left + c_right.
With min fc: binary has fc = 2 (c_left + c_right = 1), ternary has fc = 3 (c_left + c_right = 2).
2C = sum(fc - 1) = 3*1 + (n-3)*2 = 2n - 3.
C = (2n-3)/2. Not integer! So minimum fc is NOT achievable.

Next: increment one fc. Incrementing binary by 2: C += 1. Incrementing ternary by 3: C += 3/2 = 1.5 (not integer change to C).

Actually: changing fc[p] by Δfc changes 2C by Δfc, so C changes by Δfc/2.
For C to remain integer (since c values are integers and C = sum(c)):
2C must change by an even amount... wait, 2C = CL - n.
CL changes by Δfc. So 2C changes by Δfc.
C changes by Δfc/2. For C to be an integer, Δfc must be even.

Binary increment: Δfc = 2. C changes by 1. OK.
Ternary increment: Δfc = 3. C changes by 3/2. NOT OK.

So: incrementing a ternary by 3 changes C by 3/2, making C non-integer.
Starting from C = (2n-3)/2 (non-integer): adding 3/2 gives (2n-3+3)/2 = (2n)/2 = n.
C = n. CL = 2n + n = 3n.

Wait: CL = 2C + n = 2*n + n = 3n. For n=5: CL=15. But we need CL+n even: 15+5=20 even. YES.
And we need the ring system to be satisfiable with all c >= 0.

So: with one ternary incremented, CL = 3n, C = n.
But the ring system with these fc values might not have all c >= 0.

The earlier exhaustive search showed that for n=5 with single ternary increment,
the c values have negatives. But with bin+tern increment: CL = 3n + 2.
C = (3n + 2 - n)/2 = (2n+2)/2 = n+1. Integer!

For n=5: CL = 17, C = 6. This is in between the values we see (min CL = 19 at n=5).
So CL = 17 might not be achievable either.

Let me just compute the ACTUAL minimum CL for each n by checking all fc vectors.
"""
import math
from itertools import combinations, product as iproduct


def solve_edge_counts_all(n, fc, winding=1):
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
        for c0 in range(c0_min, min(c0_max + 1, c0_min + 20)):
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


print("MINIMUM CL for valid OW walks")
print("=" * 70)

for n in [5, 7, 9, 11, 13]:
    threshold = 4 * (3 ** (n - 2))
    K_MAX = 5 if n <= 7 else 4 if n <= 9 else 3
    min_cl = 999

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

        for k_tuple in iproduct(range(1, K_MAX+1), repeat=n):
            fc = [k_tuple[p] * ms[p] for p in range(n)]
            cl = sum(fc)
            if (cl + n) % 2 != 0:
                continue
            if cl >= min_cl:
                continue
            if cl > 100:
                continue

            for w in [1, -1]:
                solutions = solve_edge_counts_all(n, fc, winding=w)
                if solutions:
                    min_cl = min(min_cl, cl)
                    if n <= 9:
                        print(f"  n={n}: CL={cl}, ms={ms}, fc={fc}, w={w}")
                    break

    if min_cl < 999:
        print(f"  n={n}: MINIMUM CL = {min_cl}")
        print(f"  Binary space = 18. CL > 18? {min_cl > 18}")
        # CL for n: CL_min(n) = 2*C_min + n where C_min is the minimum total CCW count.
        # From the data: n=5 -> CL=19 -> C=7. n=7 -> CL=23 -> C=8. n=9 -> CL=?
    else:
        print(f"  n={n}: No valid walks found (K_max={K_MAX})")
