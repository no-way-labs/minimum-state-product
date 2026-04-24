#!/usr/bin/env python3
"""Check if phi is non-increasing on ALL bad steps (not just TP steps).
If yes, phi can replace FutureFc as the outer potential."""

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

    # TP adjacency
    tp_fwd = defaultdict(list)
    all_adj = defaultdict(list)
    for c in bad_list:
        e2c = exp2_count(c, n); i21c = int_21(c, n); ewc = exp2_weight(c, n)
        for i in range(n):
            new = fire(ms, fs, c, n, i)
            if new is not None and new in bad_set:
                all_adj[c].append(new)
                if exp2_count(new, n) == e2c and int_21(new, n) == i21c and exp2_weight(new, n) == ewc:
                    tp_fwd[c].append((new, fc(new, n) - fc(c, n)))

    # Compute g and phi
    g = {c: 0 for c in bad_list}
    for _ in range(3 * n):
        changed = False
        for c in bad_list:
            for s, dfc in tp_fwd.get(c, []):
                new_g = dfc + g[s]
                if new_g > g[c]: g[c] = new_g; changed = True
        if not changed: break
    phi = {c: fc(c, n) + g[c] for c in bad_list}

    # Check phi monotonicity on ALL bad steps
    phi_increase = 0
    phi_same = 0
    phi_decrease = 0
    increase_examples = []

    for c in bad_list:
        for s in all_adj[c]:
            if phi[s] > phi[c]:
                phi_increase += 1
                if len(increase_examples) < 3:
                    increase_examples.append((c, s, phi[c], phi[s], fc(c,n), fc(s,n)))
            elif phi[s] == phi[c]:
                phi_same += 1
            else:
                phi_decrease += 1

    total = phi_increase + phi_same + phi_decrease
    print(f"n={n}: {total} bad steps. phi: ↑{phi_increase} ={phi_same} ↓{phi_decrease}", end="")
    if phi_increase == 0:
        print("  *** phi NON-INCREASING on ALL bad steps! ***")
    else:
        print()
        for c, s, pc, ps, fcc, fcs in increase_examples:
            print(f"  INCREASE: phi {pc}->{ps}, fc {fcc}->{fcs}")

    # Also check: on phi-preserving steps, does the 6-tuple rank decrease (boundary)
    # and Psi decrease (interior)?
    # (This is the inner decomposition check)
