#!/usr/bin/env python3
"""
ra14_euler_check.py — Check if the edge counts form an Eulerian circuit.

A +-1 cyclic walk on the ring is equivalent to an Eulerian circuit on a multigraph
where vertex p has incoming/outgoing edges for each CW/CCW traversal.

For the walk to exist: the multigraph must have an Eulerian circuit.
Condition: the graph is connected AND every vertex has equal in-degree and out-degree.

In-degree of p: arrivals from L (e_CW(p-1)) + arrivals from R (e_CCW(p)) = fc[p].
Out-degree of p: departures to R (e_CW(p)) + departures to L (e_CCW(p-1)) = fc[p].
Equal by construction. CHECK.

Connectivity: the multigraph on vertices 0,...,n-1 with edges for CW/CCW must be connected.
This is guaranteed if fc[p] > 0 for all p (every vertex has edges) AND the graph is
on a ring (inherently connected if any edge exists on each ring edge).

Wait: the graph has edges ONLY on the ring edges (p, p+1) for each p.
The number of edges on ring edge (p, p+1) is e_CW(p) + e_CCW(p).
If e_CW(p) + e_CCW(p) = 0 for some p: the ring is disconnected!

For connectivity: need e_CW(p) + e_CCW(p) > 0 for all p.
e_CW(p) + e_CCW(p) = (c(p) + w) + c(p) = 2*c(p) + w (for winding w = +1 or -1).

For w = +1: e_CW + e_CCW = 2*c(p) + 1 >= 1. Always positive! Connected.
For w = -1: e_CW + e_CCW = 2*c(p) - 1. Could be 0 if c(p) = 0.
Wait: e_CW(p) = c(p) + w = c(p) - 1 for w = -1.
If c(p) = 0: e_CW(p) = -1. NEGATIVE! That's not valid.

Hmm, for w = -1: e_CW(p) = c(p) - 1. Need c(p) >= 1 for non-negative CW count.
But the solve_edge_counts function returns c with c(p) >= 0.
For w = -1: c(p) = 0 gives e_CW(p) = -1. This is caught by the non-negative check.

But the function uses c_CCW = c and e_CW = c + winding. For winding = -1:
e_CW = c - 1. So e_CW >= 0 requires c >= 1 for all edges.
If c(p) = 0 for some p, e_CW(p) = -1 < 0. The function should reject this.

Let me check: does solve_edge_counts return non-negative e_CW as well as c_CCW?
"""
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
        import math
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


print("Edge count analysis with Eulerian circuit check")
print("=" * 70)

for n in [7, 9, 11]:
    threshold = 4 * (3 ** (n - 2))
    print(f"\nn={n}")

    found_valid = 0
    found_euler = 0

    for bins in list(combinations(range(n), 3))[:10]:
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

        for tp in ternary_pos[:3]:
            fc = list(ms)
            fc[tp] = 6
            cl = sum(fc)
            if (cl + n) % 2 != 0:
                continue

            for w in [1, -1]:
                c = solve_edge_counts(n, fc, winding=w)
                if c is None:
                    continue

                # Check that e_CW = c + w >= 0
                e_cw = [c[p] + w for p in range(n)]
                if any(e < 0 for e in e_cw):
                    if n <= 9:
                        print(f"  ms={ms}, fc={fc}, w={w}: c={c}, e_cw={e_cw} -- NEGATIVE CW!")
                    continue

                found_valid += 1

                # Check edge connectivity
                connected = all(c[p] + e_cw[p] > 0 for p in range(n))
                if not connected:
                    print(f"  ms={ms}, fc={fc}, w={w}: DISCONNECTED")
                    continue

                found_euler += 1

                # The Eulerian circuit exists. Now verify by actual construction.
                # Use Hierholzer's algorithm.
                def find_euler_circuit(n, e_cw, e_ccw):
                    adj = {}
                    for p in range(n):
                        adj[p] = []
                        nxt_cw = (p + 1) % n
                        nxt_ccw = (p - 1) % n
                        for _ in range(e_cw[p]):
                            adj[p].append(nxt_cw)
                        for _ in range(e_ccw[p]):
                            adj[p].append(nxt_ccw)

                    # Hierholzer's algorithm
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
                    return circuit[:-1]  # Remove the duplicate end vertex

                e_ccw = c[:]
                circuit = find_euler_circuit(n, e_cw, e_ccw)

                if len(circuit) != cl:
                    print(f"  ms={ms}, fc={fc}, w={w}: Euler circuit has wrong length {len(circuit)} vs {cl}")
                    continue

                # Check fc
                fc_check = [0] * n
                for p in circuit:
                    fc_check[p] += 1
                if fc_check != fc:
                    print(f"  ms={ms}, fc={fc}, w={w}: fc mismatch: {fc_check}")
                    continue

                # Check winding
                W = 0
                for i in range(len(circuit)):
                    diff = (circuit[(i+1)%len(circuit)] - circuit[i]) % n
                    if diff == 1:
                        W += 1
                    elif diff == n - 1:
                        W -= 1
                    else:
                        print(f"  Non-+-1 step at {i}: {circuit[i]} -> {circuit[(i+1)%len(circuit)]}")
                        break

                # Check EC
                from ra14_clean_proof import check_ec
                has_ec = check_ec(circuit, n, ms)

                if abs(W) == n and n <= 9:
                    print(f"  ms={ms}, fc={fc}, w={w}: Euler circuit OK, W={W}, EC={has_ec}")
                    if not has_ec:
                        print(f"    *** NO EC: circuit={circuit}")

    print(f"  Valid edge counts: {found_valid}, with Euler circuits: {found_euler}")


if __name__ == '__main__':
    pass
