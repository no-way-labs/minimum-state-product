#!/usr/bin/env python3
"""Verify the full multi-level decomposition:
Level 1: FutureFc (non-increasing on all bad steps)
Level 2: Lex(exp2_count, exp2_weight, int_21) (non-increasing on CF steps)
Level 3: Within constant FF + TP: 720-edge 6-tuple DAG (boundary) + Psi (interior)

Check: within constant FF + constant ALL THREE TP quantities:
- Boundary with 6-tuple change: in 720-edge DAG?
- Interior (6-tuple unchanged): Psi strictly decreases?"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from itertools import product as cartesian
from collections import defaultdict

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j+1)%n])

def fire(ms, fs, c, n, i):
    L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
    out = fs[i](L, S, R)
    if out == S: return None
    lst = list(c); lst[i] = out
    return tuple(lst)

def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)
def exp2_count(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j+1)%n] != 2)
def exp2_weight(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j+1)%n] != 2)

def get_6tuple(c, n):
    return (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])

def frontierTypeVal(a, b):
    if a == b: return 0
    return (b + 3 - a) % 3

def W1(n, j):
    if j + 1 == n: return 0
    if j + 2 == n: return 1
    return j + 1

def W2(n, j):
    if j + 1 == n: return 0
    if j == 0: return n - 1
    return n - 1 - j

def psi(c, n):
    s = 0
    for j in range(n):
        a, b = c[j], c[(j+1)%n]
        if a == b: continue
        if frontierTypeVal(a, b) == 1: s += W1(n, j)
        else: s += W2(n, j)
    return s

def encode6(c0, c1, c2, cn3, cn2, cn1):
    return ((((c0 * 3 + c1) * 3 + c2) * 3 + cn3) * 3 + cn2) * 2 + cn1

# Load 720-edge phi-based DAG edges (compute them)
phi_dag_edges_cache = {}

for n in range(5, 14):
    ms, fs = build_system(n)
    all_configs = list(cartesian(*(range(m) for m in ms)))

    good_set = set()
    cur = list(tuple([0]*n))
    good_set.add(tuple(cur))
    for phase in range(3):
        rng = range(n) if phase % 2 == 0 else range(n-1, -1, -1)
        for i in rng:
            new = fire(ms, fs, tuple(cur), n, i)
            if new is not None:
                cur = list(new)
                good_set.add(tuple(cur))

    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    if len(bad_list) > 1000000:
        print(f"n={n}: skipping ({len(bad_list)} bad)")
        continue

    all_adj = defaultdict(list)
    for c in bad_list:
        for i in range(n):
            new = fire(ms, fs, c, n, i)
            if new is not None and new in bad_set:
                all_adj[c].append((new, i))

    ff = {c: fc(c, n) for c in bad_list}
    for _ in range(len(bad_list) + 1):
        changed = False
        for c in bad_list:
            for s, _ in all_adj[c]:
                if ff[s] > ff[c]: ff[c] = ff[s]; changed = True
        if not changed: break

    # Within constant FF + constant TP: check boundary (6t DAG) + interior (Psi)
    tp_const_bnd_6t_change = 0
    tp_const_bnd_6t_same_psi_down = 0
    tp_const_bnd_6t_same_psi_fail = 0
    tp_const_int_psi_down = 0
    tp_const_int_psi_fail = 0
    tp_const_int_psi_fail_examples = []

    # Also collect the 6-tuple edges within constant FF+TP
    tp_const_6t_edges = set()

    for c in bad_list:
        e2c = exp2_count(c, n); i21c = int_21(c, n); ewc = exp2_weight(c, n)
        for s, i in all_adj[c]:
            if ff[s] != ff[c]: continue  # not CF
            # Check TP constant
            if exp2_count(s, n) != e2c: continue
            if int_21(s, n) != i21c: continue
            if exp2_weight(s, n) != ewc: continue
            # Now we're in constant FF + constant TP
            s6c = get_6tuple(c, n)
            s6s = get_6tuple(s, n)
            if i <= 2 or i >= n-3:  # boundary
                if s6c != s6s:
                    tp_const_bnd_6t_change += 1
                    tp_const_6t_edges.add((s6c, s6s))
                else:
                    # Boundary fire but 6-tuple unchanged
                    if psi(s, n) < psi(c, n):
                        tp_const_bnd_6t_same_psi_down += 1
                    else:
                        tp_const_bnd_6t_same_psi_fail += 1
            else:  # interior
                if psi(s, n) < psi(c, n):
                    tp_const_int_psi_down += 1
                else:
                    tp_const_int_psi_fail += 1
                    if len(tp_const_int_psi_fail_examples) < 3:
                        tp_const_int_psi_fail_examples.append((c, s, i, psi(c,n), psi(s,n), fc(c,n), fc(s,n)))

    total_tp_const = (tp_const_bnd_6t_change + tp_const_bnd_6t_same_psi_down +
                      tp_const_bnd_6t_same_psi_fail + tp_const_int_psi_down + tp_const_int_psi_fail)
    print(f"n={n}: {total_tp_const} CF+TP-const steps")
    print(f"  Boundary 6t-change: {tp_const_bnd_6t_change} ({len(tp_const_6t_edges)} unique 6t edges)")
    print(f"  Boundary 6t-same: psi↓={tp_const_bnd_6t_same_psi_down}, fail={tp_const_bnd_6t_same_psi_fail}")
    print(f"  Interior: psi↓={tp_const_int_psi_down}, fail={tp_const_int_psi_fail}")

    for c, s, i, pc, ps, fcc, fcs in tp_const_int_psi_fail_examples:
        print(f"    INT FAIL: pos={i}, psi {pc}->{ps}, fc {fcc}->{fcs}, 6t={get_6tuple(c,n)}")
    print()
