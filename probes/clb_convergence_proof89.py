#!/usr/bin/env python3
"""
CONVERGENCE PROOF 89: LP-based pair-weight potential for TP subgraph
=====================================================================
Find w(j, a, b) such that Φ(c) = Σ_j w(j, c[j], c[j+1 mod n]) strictly
decreases on every TP edge.

For each TP edge (c → c') where position i fires:
  ΔΦ = w(i-1, c[i-1], out) - w(i-1, c[i-1], c[i])
     + w(i, out, c[i+1]) - w(i, c[i], c[i+1])
  Need: ΔΦ ≤ -1

Variables: w(j, a, b) for each position j and pair (a,b).
Minimize: max |w| or sum of w (to get simple solutions).
"""
import sys
import os
import time
import numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict


def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def int_20(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def exp2_count(c, n):
    return int_20(c, n) + int_21(c, n)

def intj_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def intj_21(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def exp2_weight(c, n):
    return intj_20(c, n) + intj_21(c, n)


def solve_lp(n_val):
    ms, fs = build_system(n_val)
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)
    n = n_val

    # Build TP edges
    tp_edges = []
    for c in bad_list:
        e2c = exp2_count(c, n)
        i21c = int_21(c, n)
        ewc = exp2_weight(c, n)
        for i in range(n):
            L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    e2s = exp2_count(succ, n)
                    i21s = int_21(succ, n)
                    ews = exp2_weight(succ, n)
                    if e2s == e2c and i21s == i21c and ews == ewc:
                        tp_edges.append((c, succ, i))

    print(f"n={n}: {len(tp_edges)} TP edges")

    # Variable indexing: w(j, a, b)
    # Position j: domain ms[j] × ms[(j+1)%n]
    # Map: var_idx[(j, a, b)] → index
    var_idx = {}
    idx = 0
    for j in range(n):
        mj = ms[j]
        mjn = ms[(j + 1) % n]
        for a in range(mj):
            for b in range(mjn):
                var_idx[(j, a, b)] = idx
                idx += 1
    n_vars = idx

    # Build constraint matrix: for each TP edge, ΔΦ ≤ -1
    # i.e., Σ [w(j,c'[j],c'[j+1]) - w(j,c[j],c[j+1])] ≤ -1
    # Only positions j=i-1 and j=i are affected
    rows = []
    for c, succ, pos in tp_edges:
        row = np.zeros(n_vars)
        # Position j = (pos-1) % n: pair changes from (c[j], c[pos]) to (c[j], out)
        j1 = (pos - 1) % n
        j2 = pos
        out = succ[pos]

        # Pair at j1: (c[j1], c[pos]) → (c[j1], out)
        a1 = c[j1]
        old_b1 = c[pos]
        new_b1 = out
        row[var_idx[(j1, a1, new_b1)]] += 1
        row[var_idx[(j1, a1, old_b1)]] -= 1

        # Pair at j2=pos: (c[pos], c[(pos+1)%n]) → (out, c[(pos+1)%n])
        b2 = c[(pos + 1) % n]
        row[var_idx[(j2, out, b2)]] += 1
        row[var_idx[(j2, c[pos], b2)]] -= 1

        rows.append(row)

    A = np.array(rows)
    b = -np.ones(len(rows))

    # Solve with scipy linprog: min c'x s.t. Ax ≤ b
    # Add bounds to keep weights small
    from scipy.optimize import linprog

    # Minimize sum of absolute values (use auxiliary variables)
    # Instead, just minimize sum of w with bounds
    # Or: find a feasible solution
    c_obj = np.zeros(n_vars)  # feasibility only

    bounds = [(-100, 100)] * n_vars

    res = linprog(c_obj, A_ub=A, b_ub=b, bounds=bounds, method='highs')
    if res.success:
        w = res.x
        print(f"  LP FEASIBLE! (pair-weight potential exists)")

        # Extract and display weights
        print(f"\n  Pair weights w(j, a, b):")
        for j in range(n):
            mj = ms[j]
            mjn = ms[(j + 1) % n]
            print(f"    Position {j} ({mj}×{mjn}):")
            for a in range(mj):
                vals = []
                for b in range(mjn):
                    v = w[var_idx[(j, a, b)]]
                    vals.append(f"{v:7.2f}")
                print(f"      a={a}: [{', '.join(vals)}]")

        # Check: are interior positions (2..n-3) uniform in their weights?
        if n >= 7:
            print(f"\n  Interior weight comparison (pos 3 vs 4):")
            m_int = 3  # interior domain
            for a in range(m_int):
                for b in range(m_int):
                    w3 = w[var_idx[(3, a, b)]]
                    w4 = w[var_idx[(4, a, b)]]
                    diff = abs(w3 - w4)
                    if diff > 0.01:
                        print(f"    w(3,{a},{b})={w3:.2f} vs w(4,{a},{b})={w4:.2f} "
                              f"DIFFER by {diff:.2f}")

        # Try to find INTEGER solution with small values
        # Round and verify
        w_int = np.round(w).astype(int)
        all_ok = True
        for c, succ, pos in tp_edges:
            j1 = (pos - 1) % n
            j2 = pos
            out = succ[pos]
            dphi = (w_int[var_idx[(j1, c[j1], out)]] - w_int[var_idx[(j1, c[j1], c[pos])]]
                    + w_int[var_idx[(j2, out, c[(pos + 1) % n])]] - w_int[var_idx[(j2, c[pos], c[(pos + 1) % n])]])
            if dphi >= 0:
                all_ok = False
                break

        if all_ok:
            print(f"\n  INTEGER solution (rounded) also works!")
            print(f"  Integer weights:")
            for j in range(n):
                mj = ms[j]
                mjn = ms[(j + 1) % n]
                print(f"    pos {j}: ", end="")
                for a in range(mj):
                    vals = [w_int[var_idx[(j, a, b)]] for b in range(mjn)]
                    print(f"  a={a}:{vals}", end="")
                print()
        else:
            print(f"\n  Rounded integer solution FAILS. Trying tighter LP...")
            # Re-solve with stronger constraint (ΔΦ ≤ -2) to allow rounding
            res2 = linprog(c_obj, A_ub=A, b_ub=-2*np.ones(len(rows)),
                          bounds=bounds, method='highs')
            if res2.success:
                w_int2 = np.round(res2.x).astype(int)
                all_ok2 = True
                for c, succ, pos in tp_edges:
                    j1 = (pos - 1) % n
                    j2 = pos
                    out = succ[pos]
                    dphi = (w_int2[var_idx[(j1, c[j1], out)]] - w_int2[var_idx[(j1, c[j1], c[pos])]]
                            + w_int2[var_idx[(j2, out, c[(pos + 1) % n])]] - w_int2[var_idx[(j2, c[pos], c[(pos + 1) % n])]])
                    if dphi >= 0:
                        all_ok2 = False
                        break
                if all_ok2:
                    print(f"  Tighter LP integer solution works!")
                    for j in range(n):
                        mj = ms[j]
                        mjn = ms[(j + 1) % n]
                        print(f"    pos {j}: ", end="")
                        for a in range(mj):
                            vals = [w_int2[var_idx[(j, a, b)]] for b in range(mjn)]
                            print(f"  a={a}:{vals}", end="")
                        print()
    else:
        print(f"  LP INFEASIBLE! (no pair-weight potential)")
        print(f"  Status: {res.message}")

    return res.success


def main():
    sys.stdout.reconfigure(line_buffering=True)
    for n_val in range(5, 10):
        t0 = time.time()
        ok = solve_lp(n_val)
        print(f"  Time: {time.time()-t0:.1f}s\n")


if __name__ == '__main__':
    main()
