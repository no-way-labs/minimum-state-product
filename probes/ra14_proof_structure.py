#!/usr/bin/env python3
"""
ra14_proof_structure.py — Analyze WHERE EC occurs to find the proof.

For each valid walk: at which proc does EC occur? Is it always at a specific type?
What's the minimum CL? What residue pattern?
"""
import math
from itertools import combinations, product as iproduct
from collections import Counter, defaultdict


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
    adj = defaultdict(list)
    for p in range(n):
        for _ in range(e_cw[p]):
            adj[p].append((p + 1) % n)
        for _ in range(c_ccw[(p - 1) % n]):
            adj[p].append((p - 1) % n)
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


def find_ec_details(word, n, ms):
    """Find first EC and return details."""
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
                    return {
                        'p': p,
                        'p_type': 'B' if ms[p] == 2 else 'T',
                        'lp_type': 'B' if ms[lp] == 2 else 'T',
                        'rp_type': 'B' if ms[rp] == 2 else 'T',
                        'sig': f"{'B' if ms[lp]==2 else 'T'}-{'B' if ms[p]==2 else 'T'}-{'B' if ms[rp]==2 else 'T'}",
                        'space': ms[lp] * ms[p] * ms[rp],
                        'fc_p': sum(1 for t in range(L) if word[t] == p),
                        's1': s1, 's2': s2,
                        'dist': abs(s2 - s1),
                    }
    return None


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


print("RA14: EC Location Analysis")
print("=" * 70)

for n in [5, 7]:
    threshold = 4 * (3 ** (n - 2))
    K_MAX = 3 if n == 7 else 4
    print(f"\nn={n}")

    ec_proc_type = Counter()
    ec_sig = Counter()
    ec_space = Counter()
    ec_fc_p = Counter()
    cl_values = Counter()
    total = 0

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
            if cl > 60:
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

                    total += 1
                    details = find_ec_details(circuit, n, ms)
                    if details:
                        ec_proc_type[details['p_type']] += 1
                        ec_sig[details['sig']] += 1
                        ec_space[details['space']] += 1
                        ec_fc_p[details['fc_p']] += 1
                        cl_values[cl] += 1

    print(f"  Total valid walks: {total}")
    print(f"  EC proc type: {dict(ec_proc_type)}")
    print(f"  EC signature: {dict(ec_sig.most_common())}")
    print(f"  EC space size: {dict(ec_space)}")
    print(f"  EC fc[p]: {dict(ec_fc_p.most_common())}")
    print(f"  CL distribution: {dict(sorted(cl_values.items()))}")

    # KEY QUESTION: What's the MINIMUM CL where valid walks exist?
    # And at that CL: what's the residue space and fc[p]?
    # If CL > 18 (binary space) for all valid walks: pigeonhole might work.
    if cl_values:
        min_cl = min(cl_values.keys())
        print(f"  Minimum CL: {min_cl}")
        print(f"  Binary space = 3*2*3 = 18. Min CL > 18? {min_cl > 18}")
