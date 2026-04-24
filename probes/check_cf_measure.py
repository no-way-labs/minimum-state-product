#!/usr/bin/env python3
"""
Check what measure strictly decreases on ALL constant-FutureFc (CF) bad steps.

Key questions:
1. Is the nonneg measure (n-fc, Psi) monotone on CF steps?
2. Does Lex(FutureFc-fc, Psi) work?
3. Does (n-fc)*K + Psi work for some K?
4. Is CF a DAG? What's the max rank?
"""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from itertools import product as cartesian
from collections import defaultdict

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j+1) % n])

def psi(c, n):
    total = 0
    for j in range(n):
        L = c[(j-1) % n]; S = c[j]; R = c[(j+1) % n]
        total += (1 if S != L else 0) + (1 if S != R else 0)
    return total

def nonneg_measure(c, n):
    return (n - fc(c, n), psi(c, n))

def compute_future_fc(bad_adj, bad_set, n):
    future_fc = {}
    for start in bad_set:
        visited = set()
        stack = [start]
        max_fc_val = fc(start, n)
        while stack:
            c = stack.pop()
            if c in visited:
                continue
            visited.add(c)
            max_fc_val = max(max_fc_val, fc(c, n))
            for s in bad_adj.get(c, []):
                if s not in visited:
                    stack.append(s)
        future_fc[start] = max_fc_val
    return future_fc

def analyze_n(n):
    ms, fs = build_system(n)
    all_configs = list(cartesian(*(range(m) for m in ms)))

    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    up_down = list(range(n)) + list(range(n-2, 0, -1))
    full = up_down * (3 * n)
    for mover in full:
        config = list(cycle[-1])
        L = config[(mover-1) % n]; S = config[mover]; R = config[(mover+1) % n]
        new_val = fs[mover](L, S, R)
        if new_val != S:
            config[mover] = new_val
            t = tuple(config)
            if t not in visited:
                visited.add(t)
                cycle.append(t)
    good_set = visited
    bad_set = set(c for c in all_configs if c not in good_set)

    bad_adj = defaultdict(list)
    for c in bad_set:
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            nv = fs[i](L, S, R)
            if nv != S:
                lst = list(c); lst[i] = nv; succ = tuple(lst)
                if succ in bad_set:
                    bad_adj[c].append(succ)

    future_fc_map = compute_future_fc(bad_adj, bad_set, n)

    cf_nonneg = 0
    cf_neg = 0
    nonneg_measure_fails = 0
    gap_psi_fail_count = 0
    K = 2 * n
    linear_fail_count = 0

    all_cf_edges = []
    for c in bad_set:
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            nv = fs[i](L, S, R)
            if nv != S:
                lst = list(c); lst[i] = nv; cp = tuple(lst)
                if cp in bad_set and future_fc_map[cp] == future_fc_map[c]:
                    all_cf_edges.append((c, cp))
                    fc_c = fc(c, n); fc_cp = fc(cp, n)
                    psi_c = psi(c, n); psi_cp = psi(cp, n)
                    nm_c = nonneg_measure(c, n)
                    nm_cp = nonneg_measure(cp, n)

                    if fc_cp >= fc_c:
                        cf_nonneg += 1
                    else:
                        cf_neg += 1

                    if nm_cp >= nm_c:
                        nonneg_measure_fails += 1

                    gap_c = future_fc_map[c] - fc_c
                    gap_cp = future_fc_map[cp] - fc_cp
                    if (gap_cp, psi_cp) >= (gap_c, psi_c):
                        gap_psi_fail_count += 1

                    lin_c = (n - fc_c) * K + psi_c
                    lin_cp = (n - fc_cp) * K + psi_cp
                    if lin_cp >= lin_c:
                        linear_fail_count += 1

    total_cf = cf_nonneg + cf_neg
    print(f"n={n}: {len(bad_set)} bad, {total_cf} CF steps "
          f"(nonneg={cf_nonneg}, neg={cf_neg})")
    print(f"  nonneg_measure fails: {nonneg_measure_fails}/{total_cf}")
    print(f"  Lex(gap, Psi) fails: {gap_psi_fail_count}/{total_cf}")
    print(f"  Linear (n-fc)*{K}+Psi fails: {linear_fail_count}/{total_cf}")

    # Check if CF is a DAG
    cf_adj = defaultdict(list)
    cf_nodes = set()
    for c, cp in all_cf_edges:
        cf_adj[c].append(cp)
        cf_nodes.add(c)
        cf_nodes.add(cp)

    WHITE, GRAY, BLACK = 0, 1, 2
    color = {v: WHITE for v in cf_nodes}
    has_cycle = False
    for start in cf_nodes:
        if color[start] != WHITE:
            continue
        stack = [(start, False)]
        while stack:
            v, processed = stack.pop()
            if processed:
                color[v] = BLACK
                continue
            if color[v] == GRAY:
                continue
            if color[v] == BLACK:
                continue
            color[v] = GRAY
            stack.append((v, True))
            for w in cf_adj.get(v, []):
                if color[w] == GRAY:
                    has_cycle = True
                elif color[w] == WHITE:
                    stack.append((w, False))

    print(f"  CF is DAG: {not has_cycle}")

    if not has_cycle:
        in_degree = defaultdict(int)
        for c in cf_nodes:
            if c not in in_degree:
                in_degree[c] = 0
        for c, cp in all_cf_edges:
            in_degree[cp] += 1
        queue = [c for c in cf_nodes if in_degree[c] == 0]
        rank = {c: 0 for c in cf_nodes}
        while queue:
            c = queue.pop(0)
            for cp in cf_adj.get(c, []):
                rank[cp] = max(rank[cp], rank[c] + 1)
                in_degree[cp] -= 1
                if in_degree[cp] == 0:
                    queue.append(cp)
        max_rank = max(rank.values()) if rank else 0
        print(f"  CF DAG max rank: {max_rank}")

    print()

for n in range(5, 13):
    analyze_n(n)
