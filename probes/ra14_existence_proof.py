#!/usr/bin/env python3
"""
ra14_existence_proof.py — Check if valid +-1 cyclic OW-NU walks exist
when the parity allows it.

For n odd (n >= 5, 7, 9): need B odd (at least one ternary at even multiplier).
The minimum such fc has one ternary at 6, rest at ms.
CL = 3(n-1) + 3 = 3n.

For n = 5: CL = 15, winding = +-5. CW = (15+5)/2 = 10, CCW = 5.
Or CW = 5, CCW = 10.

Actually: can we count the number of such walks algebraically?

A +-1 cyclic walk of length CL on Z_n with given fire counts fc[p]:
- Each step goes +1 or -1
- proc p is visited fc[p] times
- The walk is cyclic (last position -> first position is also +-1)
- Winding = CW - CCW = +-n
- Non-uniform: both CW and CCW > 0

The walk visits positions in a specific order. At position p: the walk
arrives and departs. Each visit to p contributes to fc[p].

Between consecutive visits to neighboring positions, the walk traverses the edge.
The edge (p, p+1) is traversed some number of times in each direction.

Let e_CW(p) = number of CW traversals of edge (p, p+1).
Let e_CCW(p) = number of CCW traversals of edge (p, p+1).
Then: fc[p] = e_CW(p-1) + e_CCW(p) (arrivals from left + arrivals from right)
     = e_CW(p) + e_CCW(p-1) (departures to right + departures to left)?

Actually, for a closed walk: arrivals = departures at each vertex.
fc[p] = total visits. Each visit has an arrival and a departure.
Arrivals from left (p-1->p): e_CW(p-1). Arrivals from right (p+1->p): e_CCW(p).
Departures to right (p->p+1): e_CW(p). Departures to left (p->p-1): e_CCW(p-1).
Arrival count = e_CW(p-1) + e_CCW(p) = fc[p].
Departure count = e_CW(p) + e_CCW(p-1) = fc[p].
These must be equal (closed walk).

Winding = sum of signed steps = sum_p (e_CW(p) - e_CCW(p)) = +-n.
Since e_CW(p) - e_CCW(p) is constant for all p (by closed walk), say = w.
Then n * w = +-n, so w = +-1.
So e_CW(p) = e_CCW(p) + 1 for all p (winding +n) or e_CW(p) = e_CCW(p) - 1 (winding -n).

WAIT: is e_CW(p) - e_CCW(p) constant across all edges?
From the flow equations: for a closed walk, net flow through each edge must be the same
(since it's a cycle on a ring, the net flow is constant = winding number / n... actually
the winding number IS n times the net flow per edge).

Hmm, let me think again. On a ring, the net flow through each edge is the same.
Net flow through edge (p, p+1) = e_CW(p) - e_CCW(p).
For a closed walk on a ring: the net flow is the same for every edge. Call it w.
Total winding = n * w.
For |winding| = n: |w| = 1. So w = +1 or w = -1.

For w = +1: e_CW(p) = e_CCW(p) + 1 for all p.
From fc[p] = e_CW(p-1) + e_CCW(p):
  = (e_CCW(p-1) + 1) + e_CCW(p) = e_CCW(p-1) + e_CCW(p) + 1.

Let c(p) = e_CCW(p). Then:
fc[p] = c(p-1) + c(p) + 1.

Rearranging: c(p-1) + c(p) = fc[p] - 1 for all p.

This is a linear system on n unknowns c(0), ..., c(n-1):
c(n-1) + c(0) = fc[0] - 1
c(0) + c(1) = fc[1] - 1
c(1) + c(2) = fc[2] - 1
...
c(n-2) + c(n-1) = fc[n-1] - 1

This is a TRIDIAGONAL (cyclic) system. Let me solve it.

From c(0) + c(1) = fc[1] - 1: c(1) = fc[1] - 1 - c(0).
From c(1) + c(2) = fc[2] - 1: c(2) = fc[2] - 1 - c(1) = fc[2] - 1 - (fc[1] - 1 - c(0)) = fc[2] - fc[1] + c(0).
From c(2) + c(3) = fc[3] - 1: c(3) = fc[3] - 1 - c(2) = fc[3] - 1 - fc[2] + fc[1] - c(0).

Pattern: c(k) = A(k) + (-1)^k * c(0), where A(k) depends on fc values.

The cyclic constraint is: c(n-2) + c(n-1) = fc[n-1] - 1 AND c(n-1) + c(0) = fc[0] - 1.

For a solution to exist with all c(p) >= 0 (non-negative CCW edge counts):
we need the system to be consistent AND all c(p) >= 0.

The NON-UNIFORM condition means both CW > 0 and CCW > 0.
With w = +1: e_CW(p) = c(p) + 1 >= 1 always. So CW > 0 always.
CCW > 0 iff some c(p) > 0 iff not all c(p) = 0.
If all c(p) = 0: fc[p] = 0 + 0 + 1 = 1 for all p. CL = n.
With fc[p] = ms[p]: at least some fc > 1. So c(p) > 0 for some p.

So: for odd winding with non-minimum fc, the walk is ALWAYS non-uniform!

Let me verify this and compute the edge counts.
"""
from itertools import combinations


def solve_edge_counts(n, fc, winding=1):
    """
    Solve for CCW edge counts c(p) given fire counts fc[p] and winding direction.

    System: c(p-1) + c(p) = fc[p] - winding for all p (with winding = +1 or -1).
    We solve with c(0) as free variable and check cyclic consistency.

    Returns: list of c(p) values if solution exists with all c(p) >= 0, else None.
    Also returns the constraint on c(0) for non-negative c(p).
    """
    delta = winding  # +1 for CW winding, -1 for CCW
    f = [fc[p] - delta for p in range(n)]

    # c(p-1) + c(p) = f[p]
    # c(0) + c(1) = f[1] => c(1) = f[1] - c(0)
    # c(1) + c(2) = f[2] => c(2) = f[2] - c(1) = f[2] - f[1] + c(0)
    # c(k) = A(k) + (-1)^k * c(0) where:
    # A(1) = f[1], sign(1) = -1: c(1) = f[1] - c(0)
    # A(2) = f[2] - f[1], sign(2) = +1: c(2) = f[2] - f[1] + c(0)

    # Compute A(k) and sign(k) for k = 1, ..., n-1:
    A = [0] * n
    S = [0] * n  # sign coefficient: c(k) = A[k] + S[k] * c(0)
    A[0] = 0
    S[0] = 1  # c(0) = 0 + 1 * c(0)
    for k in range(1, n):
        A[k] = f[k] - A[k-1]
        S[k] = -S[k-1]

    # Cyclic constraint: c(n-1) + c(0) = f[0]
    # (A[n-1] + S[n-1] * c(0)) + c(0) = f[0]
    # (S[n-1] + 1) * c(0) = f[0] - A[n-1]

    coeff = S[n-1] + 1
    rhs = f[0] - A[n-1]

    if coeff == 0:
        if rhs != 0:
            return None, "No solution (inconsistent)"
        # c(0) is free. Find range.
        # Need c(k) = A[k] + S[k] * c0 >= 0 for all k.
        lower = float('-inf')
        upper = float('inf')
        for k in range(n):
            if S[k] > 0:
                lower = max(lower, -A[k] / S[k])
            elif S[k] < 0:
                upper = min(upper, -A[k] / S[k])
            else:
                if A[k] < 0:
                    return None, f"No solution (A[{k}] < 0)"
        if lower > upper:
            return None, f"No solution (lower={lower} > upper={upper})"
        # Pick c0 in [lower, upper]
        import math
        c0 = math.ceil(lower) if lower > float('-inf') else 0
        c0 = max(c0, 0)
        if c0 > upper:
            return None, f"No integer solution (c0 range [{lower},{upper}])"
        c = [A[k] + S[k] * c0 for k in range(n)]
        return c, f"Free variable c(0), chose c0={c0}"
    else:
        if rhs % coeff != 0:
            return None, f"No integer solution (rhs={rhs}, coeff={coeff})"
        c0 = rhs // coeff
        c = [A[k] + S[k] * c0 for k in range(n)]
        for k in range(n):
            if c[k] < 0:
                return None, f"Negative c[{k}]={c[k]}"
        return c, f"Unique c0={c0}"


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


print("RA14: Edge Count Analysis")
print("=" * 70)

for n in [5, 7, 9, 11]:
    threshold = 4 * (3 ** (n - 2))
    print(f"\nn={n}, threshold={threshold}")
    print("-" * 50)

    for bins in list(combinations(range(n), 3))[:3]:
        bins_set = set(bins)
        ms = [2 if p in bins_set else 3 for p in range(n)]
        if not has_no_triple(ms, n):
            continue
        prod = 1
        for m in ms:
            prod *= m
        if prod >= threshold:
            continue

        # Minimum fc
        fc_min = list(ms)
        cl_min = sum(fc_min)
        c_min, info_min = solve_edge_counts(n, fc_min, winding=1)
        print(f"\n  ms={ms}, fc_min={fc_min}, CL={cl_min}")
        print(f"    Winding +1: {info_min}")
        if c_min is not None:
            ecw = [c_min[p] + 1 for p in range(n)]
            print(f"    c_CCW={c_min}, e_CW={ecw}")
            print(f"    Non-uniform: {any(c > 0 for c in c_min)}")

        # Non-minimum: one ternary doubled
        ternary_pos = [p for p in range(n) if ms[p] == 3]
        fc_mod = list(ms)
        fc_mod[ternary_pos[0]] = 6
        cl_mod = sum(fc_mod)
        c_mod, info_mod = solve_edge_counts(n, fc_mod, winding=1)
        print(f"  fc_mod={fc_mod}, CL={cl_mod}")
        print(f"    Winding +1: {info_mod}")
        if c_mod is not None:
            ecw = [c_mod[p] + 1 for p in range(n)]
            print(f"    c_CCW={c_mod}, e_CW={ecw}")
            print(f"    Non-uniform: {any(c > 0 for c in c_mod)}")
            # Check: all c(p) >= 0?
            print(f"    All c>=0: {all(c >= 0 for c in c_mod)}")

        # Try winding -1
        c_neg, info_neg = solve_edge_counts(n, fc_mod, winding=-1)
        print(f"    Winding -1: {info_neg}")
        if c_neg is not None:
            ecw = [c_neg[p] + 1 for p in range(n)]
            print(f"    c_CCW={c_neg}")
            print(f"    All c>=0: {all(c >= 0 for c in c_neg)}")

# The KEY insight: for minimum fc, the edge count system often has no solution
# with all c(p) >= 0. This would prove that no such walk exists!

print(f"\n{'='*70}")
print("COMPREHENSIVE: Check all ms/fc combos for existence of walks with winding +-1")
print("=" * 70)

for n in [5, 7, 9, 11, 13]:
    threshold = 4 * (3 ** (n - 2))
    total_combos = 0
    has_walk = 0

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

        # Check minimum fc
        fc = list(ms)
        cl = sum(fc)
        if (cl + n) % 2 == 0:  # Parity allows winding
            total_combos += 1
            for w in [1, -1]:
                c, info = solve_edge_counts(n, fc, winding=w)
                if c is not None and all(cc >= 0 for cc in c):
                    has_walk += 1
                    print(f"  n={n}: WALK EXISTS! ms={ms}, fc={fc}, winding={w}, c={c}")
                    break

        # Check single-ternary increment
        for tp in ternary_pos:
            fc2 = list(ms)
            fc2[tp] = 6
            cl2 = sum(fc2)
            if (cl2 + n) % 2 == 0:
                total_combos += 1
                for w in [1, -1]:
                    c, info = solve_edge_counts(n, fc2, winding=w)
                    if c is not None and all(cc >= 0 for cc in c):
                        has_walk += 1
                        print(f"  n={n}: WALK EXISTS! ms={ms}, fc={fc2}, winding={w}, c={c}")
                        break

        # Check double-ternary increment (odd number: 1 or 3)
        if len(ternary_pos) >= 3:
            for t1 in range(len(ternary_pos)):
                for t2 in range(t1+1, len(ternary_pos)):
                    for t3 in range(t2+1, len(ternary_pos)):
                        fc3 = list(ms)
                        fc3[ternary_pos[t1]] = 6
                        fc3[ternary_pos[t2]] = 6
                        fc3[ternary_pos[t3]] = 6
                        cl3 = sum(fc3)
                        if (cl3 + n) % 2 == 0:
                            total_combos += 1
                            for w in [1, -1]:
                                c, info = solve_edge_counts(n, fc3, winding=w)
                                if c is not None and all(cc >= 0 for cc in c):
                                    has_walk += 1
                                    print(f"  n={n}: WALK EXISTS! ms={ms}, fc={fc3}, winding={w}")
                                    break

    print(f"  n={n}: {total_combos} combos checked, {has_walk} have valid walks")
