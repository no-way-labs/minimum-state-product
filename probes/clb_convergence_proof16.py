#!/usr/bin/env python3
"""
CONVERGENCE PROOF 16: Frozen-rank determinism deep dive
========================================================

DISCOVERY (Proof15): The frozen-rank tuple (r_0,...,r_{n-1}) PERFECTLY
determines the DAG rank for n=5..8. Zero exceptions.

This means: there exists f: Z^n -> Z such that DAG_rank(c) = f(frozen_tuple(c))
for all bad configs c.

This script:
1. Verify for n=9
2. Dump the mapping f for n=5 and analyze its structure
3. Check componentwise monotonicity: if tuple A >= B componentwise,
   is f(A) >= f(B)?
4. Check if f = sum, max, or lexicographic
5. Try to identify f via regression or interpolation
6. Critical: Check if f has the PROVABLE property:
   for every valid transition c->c', f(tuple(c)) > f(tuple(c'))
   This is just verifying the DAG is a DAG (circular), but through
   the lens of frozen-rank tuples, we might see the structure.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque, Counter
import math


def compute_frozen_ranks(bad_list, bad_set, fs, ms, n):
    all_ranks = {}
    for p in range(n):
        adj = {c: [] for c in bad_list}
        for c in bad_list:
            for i in range(n):
                if i == p:
                    continue
                L = c[(i - 1) % n]
                S = c[i]
                R = c[(i + 1) % n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c)
                    lst[i] = new_S
                    succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append(succ)
        in_deg = {c: 0 for c in bad_list}
        for c in bad_list:
            for s in adj[c]:
                in_deg[s] += 1
        q = deque(c for c in bad_list if in_deg[c] == 0)
        topo = []
        while q:
            c = q.popleft()
            topo.append(c)
            for s in adj[c]:
                in_deg[s] -= 1
                if in_deg[s] == 0:
                    q.append(s)
        assert len(topo) == len(bad_list)
        rank = {}
        for c in reversed(topo):
            rank[c] = max((rank[s] + 1 for s in adj[c]), default=0)
        all_ranks[p] = rank
    return all_ranks


def compute_dag_rank(bad_list, bad_set, fs, ms, n, transitions):
    adj = {c: [] for c in bad_list}
    for c, cp, i in transitions:
        adj[c].append(cp)
    in_deg = {c: 0 for c in bad_list}
    for c in bad_list:
        for s in adj[c]:
            in_deg[s] += 1
    q = deque(c for c in bad_list if in_deg[c] == 0)
    topo = []
    while q:
        c = q.popleft()
        topo.append(c)
        for s in adj[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)
    assert len(topo) == len(bad_list), "Not a DAG!"
    rank = {}
    for c in reversed(topo):
        rank[c] = max((rank[s] + 1 for s in adj[c]), default=0)
    return rank


def analyze(n_val, verbose=False):
    ms, fs = build_system(n_val)
    n = n_val
    result = verify_system(ms, fs)
    assert result['valid']

    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    print(f"\n{'=' * 70}")
    print(f"n = {n_val}: {len(bad_list)} bad configs")
    print(f"{'=' * 70}")

    frozen = compute_frozen_ranks(bad_list, bad_set, fs, ms, n)

    transitions = []
    for c in bad_list:
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c)
                lst[i] = new_S
                succ = tuple(lst)
                if succ in bad_set:
                    transitions.append((c, succ, i))

    nt = len(transitions)

    dag_rank = compute_dag_rank(bad_list, bad_set, fs, ms, n, transitions)
    max_depth = max(dag_rank.values())

    # Frozen-rank tuples
    fr_tuple = {}
    for c in bad_list:
        fr_tuple[c] = tuple(frozen[p][c] for p in range(n))

    # Verify determinism
    fr_to_rank = {}
    for c in bad_list:
        t = fr_tuple[c]
        if t not in fr_to_rank:
            fr_to_rank[t] = dag_rank[c]
        else:
            if fr_to_rank[t] != dag_rank[c]:
                print(f"  FAILURE: tuple {t} maps to ranks {fr_to_rank[t]} and {dag_rank[c]}")
                return None

    n_unique = len(fr_to_rank)
    print(f"  {n_unique} unique frozen-rank tuples (of {len(bad_list)} configs)")
    print(f"  Frozen-rank tuple DETERMINES DAG rank: YES")
    print(f"  DAG depth: {max_depth}")

    if verbose and n_val <= 6:
        # Dump all tuples sorted by DAG rank
        sorted_tuples = sorted(fr_to_rank.items(), key=lambda x: -x[1])
        print(f"\n  Full mapping (tuple → DAG rank):")
        for t, r in sorted_tuples[:50]:
            # Count configs with this tuple
            n_configs = sum(1 for c in bad_list if fr_tuple[c] == t)
            print(f"    {t} → {r}  ({n_configs} configs)")
        if len(sorted_tuples) > 50:
            print(f"    ... ({len(sorted_tuples) - 50} more)")

    # ═══════════════════════════════════════════════════════════
    # Check componentwise monotonicity
    # ═══════════════════════════════════════════════════════════
    tuples = list(fr_to_rank.keys())
    cw_violations = 0
    cw_checked = 0
    for i in range(len(tuples)):
        for j in range(i + 1, len(tuples)):
            a, b = tuples[i], tuples[j]
            # Check if a >= b componentwise
            a_ge_b = all(a[k] >= b[k] for k in range(n))
            b_ge_a = all(b[k] >= a[k] for k in range(n))
            if a_ge_b and not b_ge_a:  # a strictly dominates b
                cw_checked += 1
                if fr_to_rank[a] < fr_to_rank[b]:
                    cw_violations += 1
            elif b_ge_a and not a_ge_b:  # b strictly dominates a
                cw_checked += 1
                if fr_to_rank[b] < fr_to_rank[a]:
                    cw_violations += 1
    print(f"\n  Componentwise monotonicity: {cw_checked} comparable pairs, "
          f"{cw_violations} violations")

    # ═══════════════════════════════════════════════════════════
    # Check sum correlation
    # ═══════════════════════════════════════════════════════════
    sums = {t: sum(t) for t in tuples}
    sum_violations = 0
    for i in range(len(tuples)):
        for j in range(i + 1, len(tuples)):
            a, b = tuples[i], tuples[j]
            if sums[a] > sums[b] and fr_to_rank[a] < fr_to_rank[b]:
                sum_violations += 1
            elif sums[b] > sums[a] and fr_to_rank[b] < fr_to_rank[a]:
                sum_violations += 1
    total_pairs = len(tuples) * (len(tuples) - 1) // 2
    print(f"  Sum monotonicity: {sum_violations} violations out of {total_pairs} pairs")

    # ═══════════════════════════════════════════════════════════
    # Check max monotonicity
    # ═══════════════════════════════════════════════════════════
    maxes = {t: max(t) for t in tuples}
    max_violations = 0
    for i in range(len(tuples)):
        for j in range(i + 1, len(tuples)):
            a, b = tuples[i], tuples[j]
            if maxes[a] > maxes[b] and fr_to_rank[a] < fr_to_rank[b]:
                max_violations += 1
            elif maxes[b] > maxes[a] and fr_to_rank[b] < fr_to_rank[a]:
                max_violations += 1
    print(f"  Max monotonicity: {max_violations} violations out of {total_pairs} pairs")

    # ═══════════════════════════════════════════════════════════
    # Check sorted_desc_lex monotonicity (as ordering on tuples)
    # ═══════════════════════════════════════════════════════════
    sorted_descs = {t: tuple(sorted(t, reverse=True)) for t in tuples}
    sdl_violations = 0
    for i in range(len(tuples)):
        for j in range(i + 1, len(tuples)):
            a, b = tuples[i], tuples[j]
            sa, sb = sorted_descs[a], sorted_descs[b]
            if sa > sb and fr_to_rank[a] < fr_to_rank[b]:
                sdl_violations += 1
            elif sb > sa and fr_to_rank[b] < fr_to_rank[a]:
                sdl_violations += 1
    print(f"  Sorted_desc_lex monotonicity: {sdl_violations} violations")

    # ═══════════════════════════════════════════════════════════
    # Check (max, sum) lex monotonicity
    # ═══════════════════════════════════════════════════════════
    ms_tuples = {t: (max(t), sum(t)) for t in tuples}
    ms_violations = 0
    for i in range(len(tuples)):
        for j in range(i + 1, len(tuples)):
            a, b = tuples[i], tuples[j]
            if ms_tuples[a] > ms_tuples[b] and fr_to_rank[a] < fr_to_rank[b]:
                ms_violations += 1
            elif ms_tuples[b] > ms_tuples[a] and fr_to_rank[b] < fr_to_rank[a]:
                ms_violations += 1
    print(f"  (max,sum)_lex monotonicity: {ms_violations} violations")

    # ═══════════════════════════════════════════════════════════
    # Linear regression: f(t) ≈ Σ w_p * t_p + b
    # ═══════════════════════════════════════════════════════════
    if n_val <= 8:
        # Simple least squares
        # X = tuples matrix, y = dag ranks
        import numpy as np
        X = np.array(tuples, dtype=float)
        y = np.array([fr_to_rank[t] for t in tuples], dtype=float)
        # Add bias
        X_bias = np.column_stack([X, np.ones(len(X))])
        try:
            w, res, _, _ = np.linalg.lstsq(X_bias, y, rcond=None)
            y_pred = X_bias @ w
            r2 = 1 - np.sum((y - y_pred) ** 2) / np.sum((y - np.mean(y)) ** 2)
            max_err = np.max(np.abs(y - y_pred))
            print(f"\n  Linear regression: R² = {r2:.4f}, max error = {max_err:.2f}")
            print(f"    Weights: {', '.join(f'{w[i]:.3f}' for i in range(n))}, bias={w[-1]:.3f}")
        except Exception:
            pass

    # ═══════════════════════════════════════════════════════════
    # KEY: Check transition-level consistency on TUPLES
    # For each transition c->c', map to tuple space.
    # Does f(tuple(c)) > f(tuple(c'))? (Must be YES by DAG.)
    # But more importantly: is the TUPLE transition pattern structured?
    # ═══════════════════════════════════════════════════════════
    print(f"\n  Transition pattern in tuple space:")
    delta_patterns = Counter()
    for c, cp, i in transitions:
        tc = fr_tuple[c]
        tcp = fr_tuple[cp]
        delta = tuple(tcp[j] - tc[j] for j in range(n))
        # Classify: which coords increase, which decrease
        incr = tuple(1 if delta[j] > 0 else (0 if delta[j] == 0 else -1)
                      for j in range(n))
        delta_patterns[incr] += 1

    print(f"  {len(delta_patterns)} distinct delta sign patterns")
    for pattern, count in sorted(delta_patterns.items(),
                                  key=lambda x: -x[1])[:15]:
        # Identify which position increases
        incr_pos = [j for j in range(n) if pattern[j] == 1]
        decr_pos = [j for j in range(n) if pattern[j] == -1]
        same_pos = [j for j in range(n) if pattern[j] == 0]
        print(f"    {pattern}: {count:>5}x  (incr:{incr_pos} decr:{decr_pos} "
              f"same:{same_pos})")

    # ═══════════════════════════════════════════════════════════
    # KEY: Check if the number of "zero-delta" positions correlates
    # with anything useful
    # ═══════════════════════════════════════════════════════════
    # For each transition, count how many frozen ranks DON'T change
    zero_counts = Counter()
    for c, cp, i in transitions:
        tc = fr_tuple[c]
        tcp = fr_tuple[cp]
        zeros = sum(1 for j in range(n) if tcp[j] == tc[j])
        zero_counts[zeros] += 1
    print(f"\n  Frozen ranks unchanged per transition:")
    for z in sorted(zero_counts.keys()):
        print(f"    {z} unchanged: {zero_counts[z]} transitions")

    return fr_to_rank


if __name__ == '__main__':
    for nv in [5, 6, 7, 8, 9]:
        prod = 4 * 3 ** (nv - 2)
        if prod > 30000:
            print(f"\n  n={nv}: computing (product {prod})...")
        v = nv <= 6
        analyze(nv, verbose=v)
