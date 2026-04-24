#!/usr/bin/env python3
"""
ra14_fixed_euler.py — Fixed Euler circuit construction.

Edge (p, p+1):
  CW traversal: p -> p+1. Count = e_CW[p].
  CCW traversal: p+1 -> p. Count = c_CCW[p].

Adjacency from vertex p:
  CW: p -> p+1. Count = e_CW[p] (CW traversals of edge (p, p+1)).
  CCW: p -> p-1. Count = c_CCW[(p-1) % n] (CCW traversals of edge (p-1, p)).
"""
import math
from itertools import combinations, product as iproduct
from collections import defaultdict


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


def find_euler_circuit_fixed(n, e_cw, c_ccw):
    """Find Euler circuit with CORRECT adjacency."""
    adj = defaultdict(list)
    for p in range(n):
        # CW: p -> (p+1) % n. Count = e_cw[p].
        for _ in range(e_cw[p]):
            adj[p].append((p + 1) % n)
        # CCW: p -> (p-1) % n. Count = c_ccw[(p-1) % n].
        for _ in range(c_ccw[(p - 1) % n]):
            adj[p].append((p - 1) % n)

    # Verify degrees
    out_deg = {p: len(adj[p]) for p in range(n)}
    expected_fc = [e_cw[(p-1)%n] + c_ccw[p] for p in range(n)]  # arrivals
    expected_out = [e_cw[p] + c_ccw[(p-1)%n] for p in range(n)]  # departures

    # Hierholzer
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
    return circuit[:-1]


def check_ec(word, n, ms):
    L = len(word)
    for p in range(n):
        lp = (p - 1) % n
        rp = (p + 1) % n
        pfc_lp = [0] * (L + 1)
        pfc_p = [0] * (L + 1)
        pfc_rp = [0] * (L + 1)
        for t in range(L):
            pfc_lp[t + 1] = pfc_lp[t] + (1 if word[t] == lp else 0)
            pfc_p[t + 1] = pfc_p[t] + (1 if word[t] == p else 0)
            pfc_rp[t + 1] = pfc_rp[t] + (1 if word[t] == rp else 0)
        mover_steps = [t for t in range(L) if word[t] == p]
        nonmover_steps = [t for t in range(L) if word[t] != p]
        for s1 in mover_steps:
            for s2 in nonmover_steps:
                if (pfc_lp[s1] % ms[lp] == pfc_lp[s2] % ms[lp] and
                    pfc_p[s1] % ms[p] == pfc_p[s2] % ms[p] and
                    pfc_rp[s1] % ms[rp] == pfc_rp[s2] % ms[rp]):
                    return True
    return False


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


# Test the specific case
n = 7
ms = [2, 2, 3, 3, 2, 3, 3]
fc = [4, 2, 3, 3, 2, 3, 6]
print(f"ms={ms}, fc={fc}")

for w in [1, -1]:
    results = solve_edge_counts_all(n, fc, winding=w)
    for c, e_cw in results:
        print(f"\nwinding={w}: c_CCW={c}, e_CW={e_cw}")

        circuit = find_euler_circuit_fixed(n, e_cw, c)
        print(f"Circuit length: {len(circuit)} (expected {sum(fc)})")

        if len(circuit) == sum(fc):
            # Check fc
            fc_check = [0] * n
            for p in circuit:
                fc_check[p] += 1
            print(f"FC match: {fc_check == fc}")

            # Check +-1
            bad = 0
            for i in range(len(circuit)):
                diff = (circuit[(i+1) % len(circuit)] - circuit[i]) % n
                if diff != 1 and diff != n - 1:
                    bad += 1
            print(f"Bad steps: {bad}")

            if bad == 0:
                W = 0
                for i in range(len(circuit)):
                    diff = (circuit[(i+1) % len(circuit)] - circuit[i]) % n
                    if diff == 1:
                        W += 1
                    else:
                        W -= 1
                print(f"Displacement: {W}")
                print(f"Circuit: {circuit}")

                has_ec = check_ec(circuit, n, ms)
                print(f"EC: {has_ec}")

# Now exhaustive search with fixed Euler construction
print(f"\n{'='*70}")
print("EXHAUSTIVE SEARCH (fixed)")
print("=" * 70)

for n in [5, 7, 9]:
    threshold = 4 * (3 ** (n - 2))
    print(f"\nn={n}")
    K_MAX = 4

    total_valid = 0
    total_ec = 0
    total_no_ec = 0

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
            if cl > 80:
                continue

            for w in [1, -1]:
                solutions = solve_edge_counts_all(n, fc, winding=w)
                for c, e_cw in solutions:
                    circuit = find_euler_circuit_fixed(n, e_cw, c)
                    if len(circuit) != cl:
                        continue
                    fc_check = [0] * n
                    for p in circuit:
                        fc_check[p] += 1
                    if fc_check != fc:
                        continue
                    bad = sum(1 for i in range(len(circuit))
                              if (circuit[(i+1)%len(circuit)] - circuit[i]) % n not in [1, n-1])
                    if bad > 0:
                        continue

                    W = sum(1 if (circuit[(i+1)%len(circuit)] - circuit[i]) % n == 1 else -1
                            for i in range(len(circuit)))
                    if abs(W) != n:
                        continue

                    total_valid += 1
                    if check_ec(circuit, n, ms):
                        total_ec += 1
                    else:
                        total_no_ec += 1
                        print(f"  NO EC! ms={ms}, fc={fc}, w={w}")

    print(f"  Valid walks: {total_valid}, EC: {total_ec}, no EC: {total_no_ec}")
