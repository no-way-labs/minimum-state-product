#!/usr/bin/env python3
"""Debug: check the specific fc=[4,2,3,3,2,3,6] case."""
import math


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


n = 7
ms = [2, 2, 3, 3, 2, 3, 3]
fc = [4, 2, 3, 3, 2, 3, 6]
cl = sum(fc)
print(f"ms={ms}, fc={fc}, CL={cl}, CL+n={cl+n}, even: {(cl+n)%2==0}")

for w in [1, -1]:
    results = solve_edge_counts_all(n, fc, winding=w)
    print(f"\nwinding={w}:")
    for c, e_cw in results:
        print(f"  c_CCW={c}, e_CW={e_cw}")

        # Build Euler circuit
        from collections import defaultdict
        adj = defaultdict(list)
        for p in range(n):
            nxt_cw = (p + 1) % n
            nxt_ccw = (p - 1) % n
            for _ in range(e_cw[p]):
                adj[p].append(nxt_cw)
            for _ in range(c[p]):
                adj[p].append(nxt_ccw)

        stack = [0]
        circuit = []
        while stack:
            v = stack[-1]
            if adj[v]:
                u = adj[v].pop()
                stack.append(u)
            else:
                circuit.append(stack.pop())
        circuit.reverse()
        circuit = circuit[:-1]

        print(f"  Circuit length: {len(circuit)} (expected {cl})")
        if len(circuit) == cl:
            # Check fc
            fc_check = [0] * n
            for p in circuit:
                fc_check[p] += 1
            print(f"  FC check: {fc_check} == {fc}? {fc_check == fc}")

            # Check +-1 steps
            bad_steps = []
            for i in range(len(circuit)):
                diff = (circuit[(i+1) % len(circuit)] - circuit[i]) % n
                if diff != 1 and diff != n - 1:
                    bad_steps.append((i, circuit[i], circuit[(i+1) % len(circuit)], diff))

            print(f"  Bad steps: {len(bad_steps)}")
            for b in bad_steps[:5]:
                print(f"    step {b[0]}: {b[1]} -> {b[2]}, diff={b[3]}")

            if not bad_steps:
                # Compute displacement
                W = 0
                for i in range(len(circuit)):
                    diff = (circuit[(i+1) % len(circuit)] - circuit[i]) % n
                    if diff == 1:
                        W += 1
                    elif diff == n - 1:
                        W -= 1
                print(f"  Displacement: {W}, |W|={abs(W)}, n={n}")
                print(f"  Circuit: {circuit}")
    if not results:
        print("  No valid solutions!")

# Also check: is this fc in the exhaustive search?
# fc = [4,2,3,3,2,3,6]
# k_tuple: k[0]=4/2=2, k[1]=2/2=1, k[2]=3/3=1, k[3]=3/3=1, k[4]=2/2=1, k[5]=3/3=1, k[6]=6/3=2
# So k = (2,1,1,1,1,1,2). All <= 4. Should be in the search.
print(f"\nk_tuple = {tuple(fc[p]//ms[p] for p in range(n))}")
print(f"All k <= 4? {all(fc[p]//ms[p] <= 4 for p in range(n))}")
