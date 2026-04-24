"""Verify LP weights are rational, round to integers, check all constraints."""
import sys, os, numpy as np
from fractions import Fraction
from collections import Counter
sys.path.insert(0, os.path.dirname(__file__))
from cup2_final_verify import T_bot, T_low, T_mid, T_high, T_top
from itertools import product as cartesian

def build_system(n):
    ms = [2] + [3]*(n-2) + [2]
    tables = [None]*n
    tables[0] = T_bot; tables[1] = T_low
    for i in range(2, n-2): tables[i] = T_mid
    tables[n-2] = T_high; tables[n-1] = T_top
    return ms, tables

def move(ms, tables, c, i):
    n = len(ms)
    L, S, R = c[(i-1)%n], c[i], c[(i+1)%n]
    new = tables[i][(L,S,R)]
    if new == S: return None
    return c[:i] + (new,) + c[i+1:]

def boundary6(c, n):
    return (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])

def build_good_cycle(n):
    def v(n, t, j):
        if t < n: return 0 if j <= t else (2 if j < n-1 else 1)
        elif t < 2*n-2:
            m = 2*n-2-t; return 0 if j < m else (2 if j < n-1 else 1)
        elif t == 2*n-2: return 1 if j == 0 else (2 if j < n-1 else 1)
        else:
            k = t-(2*n-2)
            if k == 0: return 1 if j == 0 else (2 if j < n-1 else 1)
            return 0 if j < k else (2 if j < n-1 else 1)
    return {tuple(v(n, t, j) for j in range(n)) for t in range(3*n-2)}

def pos_type(i, n):
    if i == 0: return 0
    if i == 1: return 1
    if i == 2: return 2
    if i == n-3: return 3
    if i == n-2: return 4
    if i == n-1: return 5
    return 6

n = 9
ms, tables = build_system(n)
good = build_good_cycle(n)

weight_vars = {}
idx = 0
for pt in range(7):
    for L in range(3):
        for S in range(3):
            for R in range(3):
                weight_vars[(pt, L, S, R)] = idx
                idx += 1
num_vars = idx

def potential_diff_vector(c, d, n):
    vec = np.zeros(num_vars)
    for j in range(n):
        pt = pos_type(j, n)
        L_c, S_c, R_c = c[(j-1)%n], c[j], c[(j+1)%n]
        L_d, S_d, R_d = d[(j-1)%n], d[j], d[(j+1)%n]
        key_c = (pt, L_c, S_c, R_c)
        key_d = (pt, L_d, S_d, R_d)
        if key_c in weight_vars: vec[weight_vars[key_c]] += 1
        if key_d in weight_vars: vec[weight_vars[key_d]] -= 1
    return vec

# Collect constraints
constraints = []
seen = set()
for c in cartesian(*[range(m) for m in ms]):
    if c in good: continue
    for i in range(n):
        d = move(ms, tables, c, i)
        if d is None: continue
        if d in good: continue
        bs, bd = boundary6(c, n), boundary6(d, n)
        if bs != bd:
            pair = (c, d)
            if pair not in seen:
                seen.add(pair)
                constraints.append(potential_diff_vector(c, d, n))

A = np.array(constraints)
print(f"Constraints: {len(constraints)}, Variables: {num_vars}")

# Solve LP
from scipy.optimize import linprog
n_total = num_vars + 1
c_obj = np.zeros(n_total); c_obj[-1] = 1
A1 = np.hstack([-A, np.zeros((len(constraints), 1))])
b1 = -np.ones(len(constraints))
A2 = np.hstack([np.eye(num_vars), -np.ones((num_vars, 1))])
A3 = np.hstack([-np.eye(num_vars), -np.ones((num_vars, 1))])
b23 = np.zeros(num_vars)
res = linprog(c_obj, A_ub=np.vstack([A1,A2,A3]), b_ub=np.concatenate([b1,b23,b23]),
              bounds=(None,None), method='highs')

w = res.x[:-1]
print(f"LP max weight: {res.x[-1]:.6f}")

# Analyze values
print("\nUnique weight values:")
unique = sorted(set(round(v,6) for v in w))
for v in unique:
    f = Fraction(v).limit_denominator(10)
    print(f"  {v:8.4f} -> {f} (error {abs(v-float(f)):.1e})")

# Round to half-integers
w_half = np.array([round(v*2)/2 for v in w])
print(f"\nAfter rounding to half-integers:")
print(f"  Unique values: {sorted(set(w_half))}")

# Verify
min_margin = min(row @ w_half for row in A)
print(f"  Min margin: {min_margin:.4f} (need >= 1)")
print(f"  Violations: {sum(1 for row in A if row @ w_half < 0.999)}/{len(constraints)}")

if min_margin >= 0.999:
    w_int = (w_half * 2).astype(int)
    print(f"\n=== INTEGER WEIGHTS (scale factor 2) ===")
    print(f"Unique integer values: {sorted(set(w_int))}")
    ptnames = ['P0','P1','P2','Pn3','Pn2','Pn1','mid']
    for (pt, L, S, R), i in sorted(weight_vars.items()):
        if w_int[i] != 0:
            print(f"  w({ptnames[pt]},{L},{S},{R}) = {w_int[i]}")

    # Verify at n=10,11 too
    for nn in [10, 11, 12]:
        ms2, tables2 = build_system(nn)
        good2 = build_good_cycle(nn)
        viol = 0
        total = 0
        for c in cartesian(*[range(m) for m in ms2]):
            if c in good2: continue
            for i in range(nn):
                d = move(ms2, tables2, c, i)
                if d is None: continue
                if d in good2: continue
                bs, bd = boundary6(c, nn), boundary6(d, nn)
                if bs != bd:
                    total += 1
                    psi_c = sum(w_int[weight_vars[(pos_type(j,nn), c[(j-1)%nn], c[j], c[(j+1)%nn])]] for j in range(nn))
                    psi_d = sum(w_int[weight_vars[(pos_type(j,nn), d[(j-1)%nn], d[j], d[(j+1)%nn])]] for j in range(nn))
                    if psi_d >= psi_c:
                        viol += 1
        print(f"\nn={nn}: {total} bad boundary transitions, {viol} violations")
