#!/usr/bin/env python3
"""
ra14_final_check.py — Check EC for valid walks with bin+tern increment.

Also: exhaustive search over all fc vectors to find ALL valid walks.
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
        for c0 in range(c0_min, min(c0_max + 1, c0_min + 20)):  # limit
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


def find_euler_circuit(n, e_cw_list, c_ccw_list):
    """Find an Eulerian circuit using Hierholzer's algorithm."""
    # Build adjacency list
    from collections import defaultdict
    adj = defaultdict(list)
    for p in range(n):
        nxt_cw = (p + 1) % n
        nxt_ccw = (p - 1) % n
        for _ in range(e_cw_list[p]):
            adj[p].append(nxt_cw)
        for _ in range(c_ccw_list[p]):
            adj[p].append(nxt_ccw)

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
    return circuit[:-1]  # Remove duplicate end


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
                    return True, p
    return False, -1


print("RA14 FINAL: Exhaustive FC search for valid OW walks")
print("=" * 70)

# For each n, ms: try ALL fc vectors up to some bound.
# fc[p] = k_p * ms[p]. k_p ranges from 1 to K_max.
# CL = sum(k_p * ms[p]). Need CL + n even.
# Need valid edge counts (both c_CCW >= 0 and e_CW >= 0).

for n in [5, 7, 9]:
    threshold = 4 * (3 ** (n - 2))
    print(f"\nn={n}, threshold={threshold}")

    K_MAX = 4  # max multiplier per proc

    total_fc_checked = 0
    total_valid_walks = 0
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

        # Enumerate multiplier vectors
        binary_pos = [p for p in range(n) if ms[p] == 2]
        ternary_pos = [p for p in range(n) if ms[p] == 3]

        for k_tuple in iproduct(range(1, K_MAX+1), repeat=n):
            fc = [k_tuple[p] * ms[p] for p in range(n)]
            cl = sum(fc)
            if (cl + n) % 2 != 0:
                continue
            if cl > 100:  # reasonable bound
                continue

            total_fc_checked += 1

            for w in [1, -1]:
                solutions = solve_edge_counts_all(n, fc, winding=w)
                for c_sol, e_cw_sol in solutions:
                    # Build Euler circuit
                    circuit = find_euler_circuit(n, e_cw_sol, c_sol)

                    if len(circuit) != cl:
                        continue

                    # Verify fc
                    fc_check = [0] * n
                    for p in circuit:
                        fc_check[p] += 1
                    if fc_check != fc:
                        continue

                    # Verify +-1 steps
                    valid_steps = True
                    for i in range(len(circuit)):
                        diff = (circuit[(i+1) % len(circuit)] - circuit[i]) % n
                        if diff != 1 and diff != n - 1:
                            valid_steps = False
                            break
                    if not valid_steps:
                        continue

                    total_valid_walks += 1
                    has_ec, ec_proc = check_ec(circuit, n, ms)
                    if has_ec:
                        total_ec += 1
                    else:
                        total_no_ec += 1
                        print(f"  NO EC! ms={ms}, fc={fc}, w={w}")
                        print(f"    circuit={circuit[:20]}...")

    print(f"  FC vectors checked: {total_fc_checked}")
    print(f"  Valid walks found: {total_valid_walks}")
    print(f"  With EC: {total_ec}")
    print(f"  Without EC: {total_no_ec}")

    if total_valid_walks == 0:
        print(f"  >>> NO valid OW walks exist for n={n} with K_max={K_MAX}!")
    elif total_no_ec == 0 and total_valid_walks > 0:
        print(f"  >>> ALL valid OW walks have EC for n={n}!")
