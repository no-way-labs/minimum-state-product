#!/usr/bin/env python3
"""Check if exp2_count, int_21, exp2_weight are non-increasing on CF steps.
Also check what combined measure works for decomposition."""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from itertools import product as cartesian
from collections import defaultdict, Counter

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

for n in range(7, 13):
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

    # Check TP quantities on CF steps
    e2_up = 0; e2_down = 0; e2_same = 0
    i21_up = 0; i21_down = 0; i21_same = 0
    ew_up = 0; ew_down = 0; ew_same = 0

    # Also check: (exp2_count, int_21, exp2_weight) Lex-decreasing?
    tp_lex_up = 0; tp_lex_down = 0; tp_lex_same = 0

    for c in bad_list:
        for s, i in all_adj[c]:
            if ff[s] != ff[c]: continue  # not CF

            de2 = exp2_count(s, n) - exp2_count(c, n)
            di21 = int_21(s, n) - int_21(c, n)
            dew = exp2_weight(s, n) - exp2_weight(c, n)

            if de2 > 0: e2_up += 1
            elif de2 < 0: e2_down += 1
            else: e2_same += 1

            if di21 > 0: i21_up += 1
            elif di21 < 0: i21_down += 1
            else: i21_same += 1

            if dew > 0: ew_up += 1
            elif dew < 0: ew_down += 1
            else: ew_same += 1

            # Lex (exp2_count, exp2_weight, int_21)
            tp_tuple_c = (exp2_count(c,n), exp2_weight(c,n), int_21(c,n))
            tp_tuple_s = (exp2_count(s,n), exp2_weight(s,n), int_21(s,n))
            if tp_tuple_s < tp_tuple_c: tp_lex_down += 1
            elif tp_tuple_s > tp_tuple_c: tp_lex_up += 1
            else: tp_lex_same += 1

    total = e2_up + e2_down + e2_same
    print(f"n={n}: {total} CF steps")
    print(f"  exp2_count: ↑{e2_up} ={e2_same} ↓{e2_down}")
    print(f"  int_21:     ↑{i21_up} ={i21_same} ↓{i21_down}")
    print(f"  exp2_weight:↑{ew_up} ={ew_same} ↓{ew_down}")
    print(f"  Lex(e2c,ew,i21): ↑{tp_lex_up} ={tp_lex_same} ↓{tp_lex_down}")
    print()
