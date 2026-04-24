#!/usr/bin/env python3
"""
CONVERGENCE PROOF 44: Double-Zero Edge Analysis
=================================================

Chain: (2,1) then (2,0) eliminates 63-82% of edges.
Remaining: Δint(2,1)=0 ∧ Δint(2,0)=0 edges.

TEST 1: Boundary-only LP on double-zero edges
TEST 2: Full 42-var LP on double-zero edges (check weight stability)
TEST 3: Analytical proof of Δint(2,0) ≥ 0 on zero edges
  - Same approach as proof36: examine all T_mid/T_high entries
  - On zero edges, no interior T_mid anomalous at pos ≥ 3
  - Check Δfc≤0 T_mid entries: do any create interior (2,0) pairs?
TEST 4: What pairs can change on double-zero edges?
  Count which pair types have nonzero Δ on these edges.
"""

import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system, T_mid, T_high, T_bot, T_low, T_top
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter
import numpy as np
from scipy.optimize import linprog


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def build_excursion_graph(n_val):
    ms, fs = build_system(n_val)
    n = n_val
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    anom_edges = []
    dfc_le0_adj = defaultdict(list)
    for c in bad_list:
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    dfc = delta_fc(L, S, R, out)
                    if dfc <= 0: dfc_le0_adj[c].append(succ)
                    if out != L and out != R: anom_edges.append((c, succ, i, dfc))

    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_target_map = defaultdict(list)
    for c, succ, i, dfc in anom_edges:
        anom_target_map[succ].append(c)

    exc_edges = set()
    for b in set(s for _, s, _, _ in anom_edges):
        visited = set(); queue = [b]; visited.add(b); head = 0
        while head < len(queue):
            node = queue[head]; head += 1
            if node in anom_sources:
                for src in anom_target_map.get(b, []):
                    exc_edges.add((src, node))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt); queue.append(nxt)

    return list(exc_edges), ms


def build_boundary_indices():
    idx = 0
    bnd = [{}, {}, {}, {}, {}]
    for a in range(2):
        for b in range(3):
            bnd[0][(a, b)] = idx; idx += 1
    for a in range(3):
        for b in range(3):
            bnd[1][(a, b)] = idx; idx += 1
    for a in range(3):
        for b in range(3):
            bnd[2][(a, b)] = idx; idx += 1
    for a in range(3):
        for b in range(2):
            bnd[3][(a, b)] = idx; idx += 1
    for a in range(2):
        for b in range(2):
            bnd[4][(a, b)] = idx; idx += 1
    n_bnd = idx
    return bnd, n_bnd


def feat_vector(c, n_val, bnd, n_bnd, int_idx, n_vars):
    n = n_val
    r = [0] * n_vars
    for j in range(n):
        j1 = (j + 1) % n
        a, b = c[j], c[j1]
        bnd_type = None
        if j == 0: bnd_type = 0
        elif j == 1: bnd_type = 1
        elif j == n-3: bnd_type = 2
        elif j == n-2: bnd_type = 3
        elif j == n-1: bnd_type = 4
        if bnd_type is not None:
            k = bnd[bnd_type].get((a, b))
            if k is not None: r[k] += 1
        else:
            k = int_idx[(a, b)]
            r[k] += j
    return r


def interior_delta(u, v, n, a, b):
    delta = 0
    for j in range(2, n-2):
        d_u = int(u[j] == a and u[(j+1) % n] == b)
        d_v = int(v[j] == a and v[(j+1) % n] == b)
        delta += j * (d_u - d_v)
    return delta


def main():
    bnd, n_bnd = build_boundary_indices()
    int_idx = {}
    idx = n_bnd
    for a in range(3):
        for b in range(3):
            int_idx[(a, b)] = idx; idx += 1
    n_vars = idx
    k21 = int_idx[(2, 1)]
    k20 = int_idx[(2, 0)]

    # ═══════════════════════════════════════════════════════════
    # TEST 3 FIRST: Analytical proof of Δint(2,0) ≥ 0 on zero edges
    # ═══════════════════════════════════════════════════════════
    print("=" * 70)
    print("TEST 3: Analytical proof of Δint(2,0) ≥ 0 on zero edges")
    print("=" * 70)
    print()
    print("On zero edges (Δint(2,1)=0), every step preserves interior (2,1).")
    print("Do Δfc≤0 steps also preserve interior (2,0) pairs?")
    print()
    print("A (2,0) pair at interior pos j means c[j]=2, c[j+1]=0.")
    print("Created when: c[j] changes to 2 (from non-2) with c[j+1]=0,")
    print("  OR c[j+1] changes to 0 (from non-0) with c[j]=2.")
    print()

    # Check T_mid Δfc≤0 entries: which create interior (2,0)?
    print("T_mid entries with Δfc ≤ 0 that fire:")
    n_create_20 = 0
    n_destroy_20 = 0
    n_neutral_20 = 0
    for L in range(3):
        for S in range(3):
            for R in range(3):
                out = T_mid[(L, S, R)]
                if out == S:
                    continue
                dfc = delta_fc(L, S, R, out)
                if dfc > 0:
                    continue
                # This is a Δfc≤0 firing at interior position j
                # Does it create or destroy (2,0) at pos j-1 or j?
                # Pair at j-1: (c[j-1]=L, c[j]) changes from (L,S) to (L,out)
                # Pair at j:   (c[j], c[j+1]=R) changes from (S,R) to (out,R)
                creates = False
                destroys = False
                # (2,0) at j-1: was L=2,S=0 → now L=2,out=0?
                was_20_jm1 = (L == 2 and S == 0)
                now_20_jm1 = (L == 2 and out == 0)
                # (2,0) at j: was S=2,R=0 → now out=2,R=0?
                was_20_j = (S == 2 and R == 0)
                now_20_j = (out == 2 and R == 0)

                if now_20_jm1 and not was_20_jm1:
                    creates = True
                if now_20_j and not was_20_j:
                    creates = True
                if was_20_jm1 and not now_20_jm1:
                    destroys = True
                if was_20_j and not now_20_j:
                    destroys = True

                status = "creates" if creates else ("destroys" if destroys else "neutral")
                if creates:
                    n_create_20 += 1
                elif destroys:
                    n_destroy_20 += 1
                else:
                    n_neutral_20 += 1

                if creates or destroys:
                    cls = "copy_L" if out == L else ("copy_R" if out == R else "anomalous")
                    print(f"  T_mid({L},{S},{R})→{out} Δfc={dfc} [{cls}]: {status}")
                    if creates:
                        if now_20_jm1 and not was_20_jm1:
                            print(f"    Creates (2,0) at j-1: L={L},out={out}")
                        if now_20_j and not was_20_j:
                            print(f"    Creates (2,0) at j: out={out},R={R}")

    print(f"\n  Summary: {n_create_20} create, {n_destroy_20} destroy, "
          f"{n_neutral_20} neutral")

    # Check T_high entries
    print(f"\n  T_high entries creating (2,0) at pos n-3:")
    for L in range(3):
        for S in range(3):
            for R in range(2):
                out = T_high[(L, S, R)]
                if out == S:
                    continue
                dfc = delta_fc(L, S, R, out)
                if dfc > 0:
                    continue
                # Pair at n-3: (c[n-3]=L, c[n-2]) from (L,S) to (L,out)
                now_20 = (L == 2 and out == 0)
                was_20 = (L == 2 and S == 0)
                if now_20 and not was_20:
                    print(f"    T_high({L},{S},{R})→{out}: CREATES (2,0) at n-3")

    # ═══════════════════════════════════════════════════════════
    # TEST 1: Boundary-only LP on double-zero edges
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("TEST 1: Boundary-only LP on double-zero edges")
    print("=" * 70)
    print("Δint(2,1)=0 ∧ Δint(2,0)=0 edges: boundary weights only")
    print()

    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        dbl_zero = []
        for u, v in exc_edges:
            d21 = interior_delta(u, v, n, 2, 1)
            d20 = interior_delta(u, v, n, 2, 0)
            if d21 == 0 and d20 == 0:
                dbl_zero.append((u, v))

        if not dbl_zero:
            print(f"  n={n_val}: no double-zero edges")
            continue

        ne = len(dbl_zero)
        A = np.zeros((ne, n_bnd))
        for ei, (u, v) in enumerate(dbl_zero):
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            for ki in range(n_bnd):
                A[ei, ki] = fu[ki] - fv[ki]

        c_obj = np.zeros(n_bnd)
        res = linprog(c_obj, A_ub=-A, b_ub=-np.ones(ne),
                      bounds=[(None, None)] * n_bnd, method='highs')

        dt = time.time() - t0
        status = "FEASIBLE" if res.success else "INFEASIBLE"
        print(f"  n={n_val}: {ne}/{len(exc_edges)} double-zero edges, "
              f"boundary-only: {status} ({dt:.1f}s)")

    # ═══════════════════════════════════════════════════════════
    # TEST 4: What changes on double-zero edges?
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("TEST 4: Interior pair ranges on double-zero edges")
    print("=" * 70)

    pairs = [(a, b) for a in range(3) for b in range(3)]
    for n_val in range(6, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        ranges = {p: [float('inf'), float('-inf')] for p in pairs}
        n_dz = 0

        for u, v in exc_edges:
            d21 = interior_delta(u, v, n, 2, 1)
            d20 = interior_delta(u, v, n, 2, 0)
            if d21 != 0 or d20 != 0:
                continue
            n_dz += 1
            for a, b in pairs:
                d = interior_delta(u, v, n, a, b)
                ranges[(a, b)][0] = min(ranges[(a, b)][0], d)
                ranges[(a, b)][1] = max(ranges[(a, b)][1], d)

        dt = time.time() - t0
        print(f"\n  n={n_val}: {n_dz} double-zero edges ({dt:.1f}s)")
        for a, b in pairs:
            lo, hi = ranges[(a, b)]
            if lo <= hi:
                mark = " ←MONO" if lo >= 0 and (a, b) not in [(2, 1), (2, 0)] else ""
                mark2 = " ←BOUNDED" if lo > float('-inf') and abs(lo) <= 2 else ""
                print(f"    ({a},{b}): [{lo:>4}, {hi:>4}]{mark}{mark2}")


if __name__ == '__main__':
    main()
