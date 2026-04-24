#!/usr/bin/env python3
"""Check if phi is non-increasing on CF (FutureFc-preserving) bad steps.
If so, Lex(FutureFc, phi, 6tuple-rank, Psi) works."""

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
    s = 0
    for j in range(2, n - 2):
        if c[j] == 2 and c[(j+1)%n] != 2: s += 1
    return s
def exp2_weight(c, n):
    s = 0
    for j in range(2, n - 2):
        if c[j] == 2 and c[(j+1)%n] != 2: s += j
    return s

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
        if frontierTypeVal(a, b) == 1:
            s += W1(n, j)
        else:
            s += W2(n, j)
    return s

for n in range(5, 13):
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

    # Build all-bad adjacency
    all_adj = defaultdict(list)
    for c in bad_list:
        for i in range(n):
            new = fire(ms, fs, c, n, i)
            if new is not None and new in bad_set:
                all_adj[c].append((new, i))

    # FutureFc
    ff = {c: fc(c, n) for c in bad_list}
    for _ in range(len(bad_list) + 1):
        changed = False
        for c in bad_list:
            for s, _ in all_adj[c]:
                if ff[s] > ff[c]: ff[c] = ff[s]; changed = True
        if not changed: break

    # TP + phi
    tp_fwd = defaultdict(list)
    for c in bad_list:
        e2c = exp2_count(c, n); i21c = int_21(c, n); ewc = exp2_weight(c, n)
        for s, i in all_adj[c]:
            if exp2_count(s, n) == e2c and int_21(s, n) == i21c and exp2_weight(s, n) == ewc:
                tp_fwd[c].append((s, fc(s, n) - fc(c, n)))

    g = {c: 0 for c in bad_list}
    for _ in range(3 * n):
        changed = False
        for c in bad_list:
            for s, dfc in tp_fwd.get(c, []):
                new_g = dfc + g[s]
                if new_g > g[c]: g[c] = new_g; changed = True
        if not changed: break
    phi_val = {c: fc(c, n) + g[c] for c in bad_list}

    # Check phi on CF (FutureFc-preserving) steps
    cf_phi_up = 0; cf_phi_eq = 0; cf_phi_down = 0
    cf_phi_up_examples = []

    # Also check: within BOTH FutureFc AND phi constant, what measures work?
    both_const_boundary_6t_ok = 0
    both_const_boundary_6t_fail = 0
    both_const_interior_psi_ok = 0
    both_const_interior_psi_fail = 0

    for c in bad_list:
        for s, i in all_adj[c]:
            if ff[s] != ff[c]: continue  # not CF
            if phi_val[s] > phi_val[c]:
                cf_phi_up += 1
                if len(cf_phi_up_examples) < 3:
                    cf_phi_up_examples.append((c, s, i, phi_val[c], phi_val[s]))
            elif phi_val[s] == phi_val[c]:
                cf_phi_eq += 1
                # Check inner decomposition
                s6c = (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])
                s6s = (s[0], s[1], s[2], s[n-3], s[n-2], s[n-1])
                if i <= 2 or i >= n-3:  # boundary
                    if s6c != s6s:
                        # Already verified: phi-preserving boundary = 720-edge DAG
                        both_const_boundary_6t_ok += 1
                    else:
                        # Boundary fire but 6-tuple unchanged
                        old_psi = psi(c, n); new_psi = psi(s, n)
                        if new_psi < old_psi:
                            both_const_interior_psi_ok += 1
                        else:
                            both_const_interior_psi_fail += 1
                else:  # interior
                    old_psi = psi(c, n); new_psi = psi(s, n)
                    if new_psi < old_psi:
                        both_const_interior_psi_ok += 1
                    else:
                        both_const_interior_psi_fail += 1
            else:
                cf_phi_down += 1

    total_cf = cf_phi_up + cf_phi_eq + cf_phi_down
    print(f"n={n}: {total_cf} CF steps. phi in CF: ↑{cf_phi_up} ={cf_phi_eq} ↓{cf_phi_down}")
    if cf_phi_up > 0:
        for c, s, i, pc, ps in cf_phi_up_examples:
            print(f"  phi↑: pos={i}, phi {pc}->{ps}, fc {fc(c,n)}->{fc(s,n)}, ff={ff[c]}")
    if cf_phi_eq > 0:
        print(f"  Within ff=phi=const: bnd_6t↓={both_const_boundary_6t_ok}, bnd_6t_fail={both_const_boundary_6t_fail}, int_psi↓={both_const_interior_psi_ok}, int_psi_fail={both_const_interior_psi_fail}")
    print()
