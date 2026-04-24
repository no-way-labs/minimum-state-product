#!/usr/bin/env python3
"""
CONVERGENCE PROOF 61b: Minimal — test L=3,R=3 + L=4,R=4 on jdz edges
======================================================================
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

def int_21(c, n):
    return sum(1 for j in range(2, n-2) if c[j] == 2 and c[(j+1)%n] == 1)
def int_j_20(c, n):
    return sum(j for j in range(2, n-2) if c[j] == 2 and c[(j+1)%n] == 0)

def build_feat(u, v, n, ms, nbl, nbr):
    """Extended boundary: nbl left + nbr right boundary, interior α*j+β."""
    ni = 18
    nb = 9 * (nbl + nbr)
    np_t = ni + nb
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
            base = nb
            pv = av*3+bv; pu = au*3+bu
            feat[base + pv] += j; feat[base + pu] -= j
            feat[base + 9 + pv] += 1; feat[base + 9 + pu] -= 1
    return feat, np_t

def main():
    sys.stdout.reconfigure(line_buffering=True)

    print("Building excursion graphs...", flush=True)
    edges_by_n = {}
    for n_val in range(5, 13):
        t0 = time.time()
        edges_by_n[n_val] = build_excursion_graph(n_val)
        print(f"  n={n_val}: {len(edges_by_n[n_val][0])} edges ({time.time()-t0:.1f}s)", flush=True)

    for nbl, nbr in [(2, 2), (3, 3), (4, 4), (5, 5)]:
        print(f"\n{'='*60}", flush=True)
        print(f"Config: L={nbl}, R={nbr}, interior=α*j+β", flush=True)
        print(f"{'='*60}", flush=True)

        # δ decay on jdz edges
        print(f"  {'MaxN':>5} | {'#jdz':>10} | {'δ':>10} | {'#vars':>5}", flush=True)
        for max_n in range(max(5, nbl+nbr+2), 13):
            t0 = time.time()
            feats = []
            for n_val in range(5, max_n+1):
                exc_edges, ms = edges_by_n[n_val]
                n = n_val
                if n <= nbl + nbr + 1: continue
                for u, v in exc_edges:
                    if int_21(v, n) - int_21(u, n) != 0: continue
                    if int_j_20(v, n) - int_j_20(u, n) != 0: continue
                    feat, np_t = build_feat(u, v, n, ms, nbl, nbr)
                    feats.append(feat)

            if not feats:
                print(f"  n≤{max_n:>2}  | {'(none)':>10}", flush=True)
                continue

            A = np.array(feats); E = A.shape[0]
            tv = np_t + 1
            c_obj = np.zeros(tv); c_obj[-1] = -1
            A_ub = np.zeros((E, tv)); b_ub = np.zeros(E)
            A_ub[:, :np_t] = A; A_ub[:, -1] = 1.0
            bounds = [(-1000, 1000)] * np_t + [(0, None)]
            res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')
            d = res.x[-1] if res.success else -1
            dt = time.time() - t0
            tag = " INFEASIBLE" if d <= 1e-8 else ""
            print(f"  n≤{max_n:>2}  | {E:>10} | {d:>10.4f} | {np_t:>5} ({dt:.0f}s){tag}", flush=True)

    # Also test on ALL edges (not jdz) for the best config
    print(f"\n{'='*60}", flush=True)
    print(f"ALL excursion edges: L=4,R=4", flush=True)
    print(f"{'='*60}", flush=True)
    for max_n in [11]:
        feats = []
        for n_val in range(5, max_n+1):
            exc_edges, ms = edges_by_n[n_val]
            n = n_val
            if n <= 9: continue
            for u, v in exc_edges:
                feat, np_t = build_feat(u, v, n, ms, 4, 4)
                feats.append(feat)
        if feats:
            A = np.array(feats); E = A.shape[0]
            tv = np_t + 1; c_obj = np.zeros(tv); c_obj[-1] = -1
            A_ub = np.zeros((E, tv)); b_ub = np.zeros(E)
            A_ub[:, :np_t] = A; A_ub[:, -1] = 1.0
            bounds = [(-1000, 1000)] * np_t + [(0, None)]
            res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')
            d = res.x[-1] if res.success else -1
            print(f"  n≤{max_n} ALL: δ = {d:.4f} ({E} edges, {np_t} vars)", flush=True)

            if res.success and d > 1e-6:
                p = res.x[:np_t]
                exc_12, ms_12 = edges_by_n[12]
                nf = 0; nt = 0
                for u, v in exc_12:
                    feat, _ = build_feat(u, v, 12, ms_12, 4, 4)
                    gain = -np.dot(p, feat)
                    nt += 1
                    if gain < 1e-8: nf += 1
                print(f"  n=12 test: {nf}/{nt} failures", flush=True)


if __name__ == '__main__':
    main()
