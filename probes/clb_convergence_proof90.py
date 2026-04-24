#!/usr/bin/env python3
"""
CONVERGENCE PROOF 90: LP infeasibility analysis + triple-weight test
=====================================================================
1. Extract the dual of the infeasible pair-weight LP to find the obstruction
2. Test triple-weight potential: w(j, c[j], c[j+1], c[j+2])
3. Test per-config LP (always feasible since TP is DAG, but check weight structure)
"""
import sys
import os
import time
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter


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

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def get_tp_edges(n_val):
    ms, fs = build_system(n_val)
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)
    n = n_val
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
    return tp_edges, ms, fs


def test_pair_weight_dual(n_val):
    """Find the infeasibility certificate (Farkas lemma)."""
    tp_edges, ms, fs = get_tp_edges(n_val)
    n = n_val

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

    rows = []
    for c, succ, pos in tp_edges:
        row = np.zeros(n_vars)
        j1 = (pos - 1) % n
        out = succ[pos]
        row[var_idx[(j1, c[j1], out)]] += 1
        row[var_idx[(j1, c[j1], c[pos])]] -= 1
        row[var_idx[(pos, out, c[(pos + 1) % n])]] += 1
        row[var_idx[(pos, c[pos], c[(pos + 1) % n])]] -= 1
        rows.append(row)

    A = np.array(rows)

    # Farkas: infeasible Ax ≤ b iff ∃ y ≥ 0: A'y = 0, b'y < 0
    # Here b = -1 (all), so b'y = -sum(y) < 0, i.e., sum(y) > 0
    # and A'y = 0.
    # Find y by solving: min -sum(y) s.t. A'y = 0, y ≥ 0, sum(y) ≤ 1
    n_edges = len(tp_edges)
    c_obj = -np.ones(n_edges)  # minimize -sum(y) = maximize sum(y)
    A_eq = A.T  # A'y = 0
    b_eq = np.zeros(n_vars)
    # Add sum(y) ≤ 1 as normalization
    A_ub_norm = np.ones((1, n_edges))
    b_ub_norm = np.array([1.0])
    bounds = [(0, None)] * n_edges

    res = linprog(c_obj, A_ub=A_ub_norm, b_ub=b_ub_norm,
                  A_eq=A_eq, b_eq=b_eq, bounds=bounds, method='highs')

    if res.success and -res.fun > 1e-6:
        y = res.x
        print(f"  Farkas certificate found (sum(y) = {sum(y):.6f})")

        # Which edges have positive weight?
        pos_edges = [(y[i], tp_edges[i]) for i in range(n_edges) if y[i] > 1e-8]
        pos_edges.sort(reverse=True)

        print(f"  {len(pos_edges)} edges in certificate:")
        # Show the entry types
        entry_types = Counter()
        for wt, (c, succ, pos) in pos_edges[:20]:
            L = c[(pos - 1) % n]; S = c[pos]; R = c[(pos + 1) % n]
            out = succ[pos]
            dfc = fc(succ, n) - fc(c, n)
            entry_types[(pos, L, S, R, out, dfc)] += 1
            print(f"    wt={wt:.4f} pos={pos} ({L},{S},{R})→{out} Δfc={dfc:+d} "
                  f"config={c}")

        print(f"\n  Entry type summary:")
        for (pos, L, S, R, out, dfc), cnt in sorted(entry_types.items()):
            print(f"    pos={pos} ({L},{S},{R})→{out} Δfc={dfc:+d}: {cnt}")
    else:
        print(f"  No Farkas certificate (LP might be feasible?)")


def test_triple_weight(n_val):
    """Test triple-weight potential: Φ = Σ w(j, c[j], c[j+1], c[j+2])."""
    tp_edges, ms, fs = get_tp_edges(n_val)
    n = n_val

    # Variables: w(j, a, b, c) where a=c[j], b=c[j+1], c=c[j+2]
    var_idx = {}
    idx = 0
    for j in range(n):
        mj = ms[j]
        mjn = ms[(j + 1) % n]
        mjnn = ms[(j + 2) % n]
        for a in range(mj):
            for b in range(mjn):
                for c_val in range(mjnn):
                    var_idx[(j, a, b, c_val)] = idx
                    idx += 1
    n_vars = idx

    rows = []
    for c, succ, pos in tp_edges:
        row = np.zeros(n_vars)
        out = succ[pos]

        # Affected triples: positions j = pos-2, pos-1, pos (mod n)
        for offset in [-2, -1, 0]:
            j = (pos + offset) % n
            jp1 = (j + 1) % n
            jp2 = (j + 2) % n

            # Old triple
            old_a, old_b, old_c = c[j], c[jp1], c[jp2]
            new_a, new_b, new_c = succ[j], succ[jp1], succ[jp2]

            if (old_a, old_b, old_c) != (new_a, new_b, new_c):
                row[var_idx[(j, new_a, new_b, new_c)]] += 1
                row[var_idx[(j, old_a, old_b, old_c)]] -= 1

        rows.append(row)

    A = np.array(rows)
    b = -np.ones(len(rows))
    c_obj = np.zeros(n_vars)
    bounds = [(-200, 200)] * n_vars

    res = linprog(c_obj, A_ub=A, b_ub=b, bounds=bounds, method='highs')
    if res.success:
        print(f"  Triple-weight LP FEASIBLE! ✓")
        w = res.x

        # Show interior weights (positions 2..n-3)
        if n >= 7:
            print(f"  Interior weight comparison (pos 3 vs 4):")
            diffs = []
            for a in range(3):
                for b in range(3):
                    for c_val in range(3):
                        w3 = w[var_idx[(3, a, b, c_val)]]
                        w4 = w[var_idx[(4, a, b, c_val)]]
                        d = abs(w3 - w4)
                        diffs.append(d)
                        if d > 0.5:
                            print(f"    w(3,{a},{b},{c_val})={w3:.1f} vs "
                                  f"w(4,{a},{b},{c_val})={w4:.1f}")
            print(f"    Max diff: {max(diffs):.2f}, Mean diff: {sum(diffs)/len(diffs):.2f}")
    else:
        print(f"  Triple-weight LP INFEASIBLE!")


def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in [5, 6, 7]:
        t0 = time.time()
        print(f"\n{'='*70}")
        print(f"n={n_val}:")

        print(f"\n  --- Pair-weight dual (Farkas certificate) ---")
        test_pair_weight_dual(n_val)

        print(f"\n  --- Triple-weight test ---")
        test_triple_weight(n_val)

        print(f"  Time: {time.time()-t0:.1f}s")

    # Also test n=8,9 for triple-weight only
    for n_val in [8, 9]:
        t0 = time.time()
        print(f"\n{'='*70}")
        print(f"n={n_val}: triple-weight only")
        test_triple_weight(n_val)
        print(f"  Time: {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
