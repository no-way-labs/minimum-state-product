"""LP search for a syntactic potential decreasing on all bad boundary transitions.

Potential: Psi(c) = sum_j w(pos_type(j), c[j-1], c[j], c[j+1])
where w is a weight function on (position_type, L, S, R).

For each bad boundary transition c -> d:
  Psi(c) > Psi(d)  i.e.  Psi(c) - Psi(d) >= 1

This is a linear program in the weights w.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_final_verify import T_bot, T_low, T_mid, T_high, T_top
from itertools import product as cartesian
import numpy as np

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
    return 6  # mid

# Weight index: (pos_type, L, S, R) -> column in LP
# pos_types: 0-6 (7 types)
# L,S,R each in {0,1,2} but constrained by ms
# Just enumerate all valid (pos_type, L, S, R) tuples

n = 9
ms, tables = build_system(n)
good = build_good_cycle(n)

# Enumerate weight variables
weight_vars = {}
idx = 0
for pt in range(7):
    for L in range(3):
        for S in range(3):
            for R in range(3):
                weight_vars[(pt, L, S, R)] = idx
                idx += 1
num_vars = idx
print(f"Weight variables: {num_vars}")

def potential_diff_vector(c, d, n):
    """Return the coefficient vector for Psi(c) - Psi(d) in terms of weight variables."""
    vec = np.zeros(num_vars)
    for j in range(n):
        pt = pos_type(j, n)
        L_c, S_c, R_c = c[(j-1)%n], c[j], c[(j+1)%n]
        L_d, S_d, R_d = d[(j-1)%n], d[j], d[(j+1)%n]
        key_c = (pt, L_c, S_c, R_c)
        key_d = (pt, L_d, S_d, R_d)
        if key_c in weight_vars:
            vec[weight_vars[key_c]] += 1
        if key_d in weight_vars:
            vec[weight_vars[key_d]] -= 1
    return vec

# Collect ALL bad boundary-changing transitions
print("Collecting bad boundary transitions...")
t0 = time.time()
constraints = []  # each is a vector v such that v @ w >= 1

seen_pairs = set()
for c in cartesian(*[range(m) for m in ms]):
    if c in good: continue
    for i in range(n):
        d = move(ms, tables, c, i)
        if d is None: continue
        if d in good: continue
        bs, bd = boundary6(c, n), boundary6(d, n)
        if bs != bd:
            pair = (c, d)
            if pair not in seen_pairs:
                seen_pairs.add(pair)
                constraints.append(potential_diff_vector(c, d, n))

print(f"Constraints: {len(constraints)} unique transitions, time: {time.time()-t0:.1f}s")

# Solve LP: find w such that A @ w >= 1 for all constraints
# Minimize ||w||_1 (or just find feasibility)
A = np.array(constraints)
print(f"Constraint matrix: {A.shape}")

# Check rank
rank = np.linalg.matrix_rank(A)
print(f"Matrix rank: {rank} (out of {num_vars} variables)")

# Try scipy LP
try:
    from scipy.optimize import linprog
    # minimize sum(w) subject to A @ w >= 1
    # linprog minimizes c @ x subject to A_ub @ x <= b_ub
    # So: minimize sum(w) subject to -A @ w <= -1
    c_obj = np.ones(num_vars)
    res = linprog(c_obj, A_ub=-A, b_ub=-np.ones(len(constraints)), 
                  bounds=(None, None), method='highs')
    # Reformulate: minimize max |w_i| with A @ w >= 1
    n_total = num_vars + 1  # extra variable t for max
    c_obj2 = np.zeros(n_total)
    c_obj2[-1] = 1
    # -A @ w <= -1
    A1 = np.hstack([-A, np.zeros((len(constraints), 1))])
    b1 = -np.ones(len(constraints))
    # w_i - t <= 0 and -w_i - t <= 0
    A2 = np.hstack([np.eye(num_vars), -np.ones((num_vars, 1))])
    A3 = np.hstack([-np.eye(num_vars), -np.ones((num_vars, 1))])
    b23 = np.zeros(num_vars)
    A_all = np.vstack([A1, A2, A3])
    b_all = np.concatenate([b1, b23, b23])

    res2 = linprog(c_obj2, A_ub=A_all, b_ub=b_all, bounds=(None, None), method='highs')
    if res2.success:
        print(f"\nFEASIBLE! Syntactic potential EXISTS.")
        print(f"Max weight magnitude: {res2.x[-1]:.4f}")
        w = res2.x[:-1]
        nonzero = [(k, w[v]) for k, v in weight_vars.items() if abs(w[v]) > 0.01]
        nonzero.sort(key=lambda x: -abs(x[1]))
        print(f"Nonzero weights: {len(nonzero)}")
        for (pt, L, S, R), val in nonzero[:20]:
            ptname = ['P0','P1','P2','Pn3','Pn2','Pn1','mid'][pt]
            print(f"  w({ptname},{L},{S},{R}) = {val:.4f}")
    else:
        print(f"\nINFEASIBLE. No syntactic local-window potential exists.")
        print(f"Status: {res2.message}")
except ImportError:
    print("scipy not available, skipping LP")

print(f"\nTotal time: {time.time()-t0:.1f}s")
