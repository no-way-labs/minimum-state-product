#!/usr/bin/env python3
"""
CONVERGENCE PROOF 63: δ decay analysis for polynomial bases
============================================================
For each polynomial degree d and boundary size BL:
  Train on n=5..N (cumulative), record δ(N).
Key question: does δ stabilize or → 0?

Also: per-n δ for cubic basis (how fast does each n's gap shrink?)
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

    # === Part 1: Per-n δ for cubic and quartic ===
    print(f"\n{'='*70}", flush=True)
    print("PER-N δ: how does the gap for a single n scale?", flush=True)
    print("="*70, flush=True)

    bases = {
        'j,1': [lambda j,n:j, lambda j,n:1],
        'j²,j,1': [lambda j,n:j*j, lambda j,n:j, lambda j,n:1],
        'j³,j²,j,1': [lambda j,n:j**3, lambda j,n:j*j, lambda j,n:j, lambda j,n:1],
        'j⁴,..,1': [lambda j,n:j**4, lambda j,n:j**3, lambda j,n:j*j, lambda j,n:j, lambda j,n:1],
    }

    for nbl in [2, 3]:
        nbr = nbl
        print(f"\nBL={nbl}:", flush=True)
        header = f"  {'n':>3}"
        for bname in bases:
            header += f" {'δ('+bname+')':>14}"
        print(header, flush=True)

        for n_val in range(max(5, nbl+nbr+2), 13):
            line = f"  {n_val:>3}"
            for bname, bfuncs in bases.items():
                feats = []
                for u, v in jdz_by_n[n_val]:
                    feat, np_t = build_feat(u, v, n_val, bfuncs, nbl, nbr)
                    feats.append(feat)
                if feats:
                    _, d = solve_lp(feats, np_t)
                    line += f" {d:>14.1f}" if d > 1e-8 else f" {'FAIL':>14}"
                else:
                    line += f" {'(none)':>14}"
            print(line, flush=True)

    # === Part 2: Cumulative δ decay ===
    print(f"\n{'='*70}", flush=True)
    print("CUMULATIVE δ: train on n=5..N, how does δ(N) decay?", flush=True)
    print("="*70, flush=True)

    for nbl in [2, 3]:
        nbr = nbl
        print(f"\nBL={nbl}:", flush=True)
        header = f"  {'N':>3}"
        for bname in bases:
            header += f" {'δ≤N('+bname+')':>14}"
        print(header, flush=True)

        for max_n in range(max(5, nbl+nbr+2), 13):
            line = f"  {max_n:>3}"
            for bname, bfuncs in bases.items():
                feats = []
                np_t = None
                for n_val in range(5, max_n+1):
                    if n_val <= nbl + nbr + 1: continue
                    for u, v in jdz_by_n[n_val]:
                        feat, np_t = build_feat(u, v, n_val, bfuncs, nbl, nbr)
                        feats.append(feat)
                if feats:
                    _, d = solve_lp(feats, np_t)
                    line += f" {d:>14.1f}" if d > 1e-8 else f" {'FAIL':>14}"
                else:
                    line += f" {'(none)':>14}"
            print(line, flush=True)

    # === Part 3: Weight extraction for cubic BL=2 ===
    print(f"\n{'='*70}", flush=True)
    print("WEIGHT ANALYSIS: cubic BL=2, trained n≤12", flush=True)
    print("="*70, flush=True)

    bfuncs = bases['j³,j²,j,1']
    nbl = nbr = 2
    feats = []
    for n_val in range(5, 13):
        if n_val <= nbl + nbr + 1: continue
        for u, v in jdz_by_n[n_val]:
            feat, np_t = build_feat(u, v, n_val, bfuncs, nbl, nbr)
            feats.append(feat)

    weights, delta = solve_lp(feats, np_t)
    print(f"δ = {delta:.4f}, {np_t} params, {len(feats)} edges", flush=True)

    if weights is not None and delta > 1e-6:
        nb = 9 * (nbl + nbr)
        # Boundary weights
        for side, offset in [("Left", 0), ("Right", 9*nbl)]:
            for pos in range(nbl if side == "Left" else nbr):
                print(f"\n  {side} boundary pos {pos}:", flush=True)
                base = offset + 9 * pos
                for a in range(3):
                    vals = [f"{weights[base + a*3+b]:8.2f}" for b in range(3)]
                    print(f"    a={a}: {' '.join(vals)}", flush=True)

        # Interior: 4 basis functions × 9 pair types
        basis_names = ['j³', 'j²', 'j', '1']
        for k, bn in enumerate(basis_names):
            print(f"\n  Interior coeff of {bn}:", flush=True)
            base = nb + 9 * k
            for a in range(3):
                vals = [f"{weights[base + a*3+b]:8.2f}" for b in range(3)]
                print(f"    a={a}: {' '.join(vals)}", flush=True)

        # Reconstruct w(j, a, b) for each pair type at sample positions
        print(f"\n  Reconstructed w(j, a=2, b=1) [the key pair]:", flush=True)
        for n_val in [8, 10, 12]:
            vals = []
            for j in range(n_val):
                if j < nbl:
                    w = weights[9*j + 2*3+1]
                elif j >= n_val - nbr:
                    w = weights[9*nbl + 9*(j-(n_val-nbr)) + 2*3+1]
                else:
                    w = sum(weights[nb + 9*k + 2*3+1] * bfuncs[k](j, n_val)
                            for k in range(len(bfuncs)))
                vals.append(w)
            print(f"    n={n_val}: {' '.join(f'{v:7.1f}' for v in vals)}", flush=True)

if __name__ == '__main__':
    main()
