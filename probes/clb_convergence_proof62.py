#!/usr/bin/env python3
"""
CONVERGENCE PROOF 62: Parametric LP on jdz edges
=================================================
Test polynomial and relative-position bases to find universal potential.
"""
import sys, os, time
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict

def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))

def build_excursion_graph(n_val):
    ms, fs = build_system(n_val)
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)
    anom_edges = []
    dfc_le0_adj = defaultdict(list)
    for c in bad_list:
        for i in range(n_val):
            L = c[(i-1) % n_val]; S = c[i]; R = c[(i+1) % n_val]
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
        visited = {b}; queue = [b]; head = 0
        while head < len(queue):
            node = queue[head]; head += 1
            if node in anom_sources:
                for src in anom_target_map.get(b, []):
                    exc_edges.add((src, node))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt); queue.append(nxt)
    return list(exc_edges), ms

def int_21(c, n):
    return sum(1 for j in range(2, n-2) if c[j] == 2 and c[(j+1)%n] == 1)
def int_j_20(c, n):
    return sum(j for j in range(2, n-2) if c[j] == 2 and c[(j+1)%n] == 0)

def build_feat(u, v, n, basis_funcs, nbl, nbr):
    nb = 9 * (nbl + nbr)
    ni = 9 * len(basis_funcs)
    np_t = nb + ni
    feat = np.zeros(np_t)
    for j in range(n):
        au, bu = u[j], u[(j+1) % n]
        av, bv = v[j], v[(j+1) % n]
        if au == av and bu == bv: continue
        if j < nbl:
            base = 9 * j
            feat[base + av*3+bv] += 1; feat[base + au*3+bu] -= 1
        elif j >= n - nbr:
            base = 9 * nbl + 9 * (j - (n - nbr))
            feat[base + av*3+bv] += 1; feat[base + au*3+bu] -= 1
        else:
            for k, bf in enumerate(basis_funcs):
                val = bf(j, n)
                base = nb + 9 * k
                feat[base + av*3+bv] += val; feat[base + au*3+bu] -= val
    return feat, np_t

def solve_lp(feats, np_t):
    if not feats: return None, 0
    A = np.array(feats); E = A.shape[0]
    tv = np_t + 1
    c_obj = np.zeros(tv); c_obj[-1] = -1
    A_ub = np.zeros((E, tv)); b_ub = np.zeros(E)
    A_ub[:, :np_t] = A; A_ub[:, -1] = 1.0
    bounds = [(-1000, 1000)] * np_t + [(0, None)]
    res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')
    if res.success: return res.x[:np_t], res.x[-1]
    return None, -1

def main():
    sys.stdout.reconfigure(line_buffering=True)

    print("Building excursion graphs...", flush=True)
    data = {}
    for n_val in range(5, 13):
        t0 = time.time()
        edges, ms = build_excursion_graph(n_val)
        data[n_val] = (edges, ms)
        print(f"  n={n_val}: {len(edges)} exc edges ({time.time()-t0:.1f}s)", flush=True)

    # Extract jdz edges
    jdz_by_n = {}
    for n_val, (edges, ms) in data.items():
        jdz = list(set((u,v) for u,v in edges
                   if int_21(v,n_val)-int_21(u,n_val)==0
                   and int_j_20(v,n_val)-int_j_20(u,n_val)==0))
        jdz_by_n[n_val] = jdz
        print(f"  n={n_val}: {len(jdz)} jdz edges", flush=True)

    # Basis families — using default args to capture values
    bases = [
        ('j,1',         [lambda j,n:j, lambda j,n:1]),
        ('t,1',         [lambda j,n:j/(n-1), lambda j,n:1]),
        ('j²,j,1',      [lambda j,n:j*j, lambda j,n:j, lambda j,n:1]),
        ('t²,t,1',      [lambda j,n:(j/(n-1))**2, lambda j,n:j/(n-1), lambda j,n:1]),
        ('jN-j²,j,1',   [lambda j,n:j*(n-1-j), lambda j,n:j, lambda j,n:1]),
        ('j³,j²,j,1',   [lambda j,n:j**3, lambda j,n:j*j, lambda j,n:j, lambda j,n:1]),
        ('t³,t²,t,1',   [lambda j,n:(j/(n-1))**3, lambda j,n:(j/(n-1))**2, lambda j,n:j/(n-1), lambda j,n:1]),
        ('1/j+,j,1',    [lambda j,n:1.0/(j+1), lambda j,n:j, lambda j,n:1]),
        ('1/Nj,j,1',    [lambda j,n:1.0/(n-j), lambda j,n:j, lambda j,n:1]),
        ('1/j+,1/Nj,j,1', [lambda j,n:1.0/(j+1), lambda j,n:1.0/(n-j), lambda j,n:j, lambda j,n:1]),
    ]

    print(f"\n{'Basis':22s} {'BL':>2} {'#p':>3} {'n≤11 #e':>9} {'δ≤11':>7} {'n≤12 #e':>9} {'δ≤12':>7}", flush=True)
    print("-" * 68, flush=True)

    for bname, bfuncs in bases:
        for nbl in [2, 3, 4]:
            nbr = nbl
            feats_11 = []; feats_12 = []; np_t = None
            for n_val in range(5, 13):
                if n_val <= nbl + nbr + 1: continue
                for u, v in jdz_by_n[n_val]:
                    feat, np_t = build_feat(u, v, n_val, bfuncs, nbl, nbr)
                    if n_val <= 11:
                        feats_11.append(feat)
                    feats_12.append(feat)

            if np_t is None: continue
            _, d11 = solve_lp(feats_11, np_t) if feats_11 else (None, 0)
            _, d12 = solve_lp(feats_12, np_t) if feats_12 else (None, 0)
            s11 = f"{d11:.1f}" if d11 > 1e-8 else "FAIL"
            s12 = f"{d12:.1f}" if d12 > 1e-8 else "FAIL"
            ne11 = len(feats_11); ne12 = len(feats_12)
            print(f"  {bname:20s} {nbl:>2} {np_t:>3} {ne11:>9} {s11:>7} {ne12:>9} {s12:>7}", flush=True)

    # === Part 2: ALL excursion edges with best bases ===
    print(f"\n{'='*68}", flush=True)
    print(f"ALL EXCURSION EDGES (train n≤11, test n=12)", flush=True)
    print(f"{'='*68}", flush=True)

    for bname, bfuncs in [('t²,t,1', bases[3][1]),
                           ('jN-j²,j,1', bases[4][1]),
                           ('1/j+,1/Nj,j,1', bases[9][1])]:
        for nbl in [2, 3]:
            nbr = nbl
            feats = []; np_t = None
            for n_val in range(5, 12):
                if n_val <= nbl + nbr + 1: continue
                edges, ms = data[n_val]
                for u, v in set(edges):
                    feat, np_t = build_feat(u, v, n_val, bfuncs, nbl, nbr)
                    feats.append(feat)
            if not feats: continue
            weights, delta = solve_lp(feats, np_t)
            tag = f"{delta:.1f}" if delta > 1e-8 else "FAIL"
            n12_info = ""
            if delta > 1e-6 and weights is not None:
                edges_12 = set(data[12][0])
                fails = total = 0
                for u, v in edges_12:
                    feat, _ = build_feat(u, v, 12, bfuncs, nbl, nbr)
                    gain = -feat @ weights
                    total += 1
                    if gain < 1e-8: fails += 1
                n12_info = f" n12:{fails}/{total}"
            print(f"  {bname:20s} L={nbl}: {len(feats):>8} edges, δ={tag:>7}{n12_info}", flush=True)

if __name__ == '__main__':
    main()
