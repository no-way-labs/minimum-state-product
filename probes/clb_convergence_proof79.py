#!/usr/bin/env python3
"""
CONVERGENCE PROOF 79: LP-based potential search + hard-edge analysis
====================================================================
Two approaches:
1. LP formulation: find weights w such that Φ = Σ w_i * feature_i(c)
   strictly decreases on every jdz edge.
2. Detailed analysis of "hard edges" (Δfc<0, Δrank_up>0): what changes
   in the interior that makes full_rank drop?
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter, deque

def delta_fc_val(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])

def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def int_j_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def int_j_21(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def int_20(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def build_jdz_graph(n_val):
    ms, fs = build_system(n_val)
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)
    n = n_val
    anom_edges = []
    dfc_le0_adj = defaultdict(list)
    for c in bad_list:
        for i in range(n):
            L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    dfc = delta_fc_val(L, S, R, out)
                    if dfc <= 0:
                        dfc_le0_adj[c].append(succ)
                    if out != L and out != R:
                        anom_edges.append((c, succ, i, dfc))
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
    jdz = [(u,v) for u,v in exc_edges
           if int_21(v,n) == int_21(u,n) and int_j_20(v,n) == int_j_20(u,n)]
    return jdz, ms, fs

def compute_features(c, n, rank_up_val):
    """Compute a feature vector for config c."""
    feats = {}
    feats['fc'] = fc(c, n)
    feats['rank_up'] = rank_up_val
    feats['P0'] = c[0]
    feats['P1'] = c[1]
    feats['Pn2'] = c[n-2]
    feats['Pn1'] = c[n-1]
    feats['bdry_sum'] = c[0] + c[1] + c[n-2] + c[n-1]
    # Interior features
    interior = c[2:n-2]
    feats['int_sum'] = sum(interior)
    feats['int_n0'] = sum(1 for x in interior if x == 0)
    feats['int_n1'] = sum(1 for x in interior if x == 1)
    feats['int_n2'] = sum(1 for x in interior if x == 2)
    feats['int_wsum'] = sum((j-2) * c[j] for j in range(2, n-2))
    # Number of interior transitions (within interior only)
    feats['int_fc'] = sum(1 for j in range(2, n-3) if c[j] != c[j+1])
    # Rightmost position with value 2
    feats['right2'] = max((j for j in range(2, n-2) if c[j] == 2), default=0)
    # Leftmost position with value 0
    feats['left0'] = min((j for j in range(2, n-2) if c[j] == 0), default=n)
    # Number of (1,0) pairs in interior
    feats['int_10'] = sum(1 for j in range(2, n-3) if c[j] == 1 and c[j+1] == 0)
    # Number of (0,1) pairs in interior
    feats['int_01'] = sum(1 for j in range(2, n-3) if c[j] == 0 and c[j+1] == 1)
    return feats

def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in [7, 8, 9, 10]:
        t0 = time.time()
        jdz, ms, fs = build_jdz_graph(n_val)
        n = n_val
        if not jdz:
            continue

        # Build adjacency and DAG rank
        jdz_adj = defaultdict(list)
        jdz_nodes = set()
        for u, v in jdz:
            jdz_adj[u].append(v)
            jdz_nodes.add(u); jdz_nodes.add(v)

        # Rank_up
        up_adj = defaultdict(list)
        up_nodes = set()
        for u, v in jdz:
            if fc(v, n) >= fc(u, n):
                up_adj[u].append(v); up_nodes.add(u); up_nodes.add(v)
        id_up = defaultdict(int)
        for u in up_nodes:
            for v in up_adj[u]: id_up[v] += 1
        q = deque([u for u in up_nodes if id_up[u] == 0])
        t_up = []
        while q:
            nd = q.popleft(); t_up.append(nd)
            for nx in up_adj[nd]:
                id_up[nx] -= 1
                if id_up[nx] == 0: q.append(nx)
        rank_up = {}
        for c in reversed(t_up):
            rank_up[c] = max((rank_up[s]+1 for s in up_adj[c]), default=0)

        # Full DAG rank
        id_f = defaultdict(int)
        for u, v in jdz: id_f[v] += 1
        q = deque([u for u in jdz_nodes if id_f[u] == 0])
        topo = []
        while q:
            nd = q.popleft(); topo.append(nd)
            for nx in jdz_adj[nd]:
                id_f[nx] -= 1
                if id_f[nx] == 0: q.append(nx)
        assert len(topo) == len(jdz_nodes)
        full_rank = {}
        for c in reversed(topo):
            full_rank[c] = max((full_rank[s]+1 for s in jdz_adj[c]), default=0)

        print(f"\n{'='*70}", flush=True)
        print(f"n={n}: {len(jdz)} jdz edges ({time.time()-t0:.1f}s)", flush=True)

        # === LP-based potential search ===
        try:
            from scipy.optimize import linprog
            has_scipy = True
        except ImportError:
            has_scipy = False

        feat_names = ['fc', 'rank_up', 'P0', 'P1', 'Pn2', 'Pn1', 'bdry_sum',
                       'int_sum', 'int_n0', 'int_n1', 'int_n2', 'int_wsum',
                       'int_fc', 'right2', 'left0', 'int_10', 'int_01']

        if has_scipy and len(jdz) <= 200000:
            import numpy as np
            # For each edge (u,v): Σ w_i * (feat_i(u) - feat_i(v)) >= 1
            feat_cache = {}
            for c in jdz_nodes:
                feat_cache[c] = compute_features(c, n, rank_up.get(c, 0))

            nf = len(feat_names)
            A_ub = np.zeros((len(jdz), nf))
            b_ub = np.full(len(jdz), -1.0)  # -(feat(u)-feat(v)) @ w <= -1

            for idx, (u, v) in enumerate(jdz):
                fu = feat_cache[u]
                fv = feat_cache[v]
                for j, fname in enumerate(feat_names):
                    A_ub[idx, j] = -(fu[fname] - fv[fname])

            # Minimize 0 (feasibility problem)
            c_obj = np.zeros(nf)

            # Bound weights to [-100, 100] for numerical stability
            bounds = [(-100, 100)] * nf

            result_lp = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds,
                                method='highs')

            if result_lp.success:
                w = result_lp.x
                print(f"\n  LP FEASIBLE! Weights:", flush=True)
                for j, fname in enumerate(feat_names):
                    if abs(w[j]) > 0.01:
                        print(f"    {fname}: {w[j]:.4f}", flush=True)

                # Verify
                viol = 0
                for u, v in jdz:
                    fu = feat_cache[u]; fv = feat_cache[v]
                    phi_u = sum(w[j] * fu[fname] for j, fname in enumerate(feat_names))
                    phi_v = sum(w[j] * fv[fname] for j, fname in enumerate(feat_names))
                    if phi_v >= phi_u:
                        viol += 1
                print(f"  Verification: {viol}/{len(jdz)} violations", flush=True)
            else:
                print(f"\n  LP INFEASIBLE with {nf} features", flush=True)
                print(f"  Status: {result_lp.message}", flush=True)

                # Try adding more features: pair counts, position-specific
                extra_feats = []
                for j in range(2, n-2):
                    for val in [0, 1, 2]:
                        extra_feats.append((f'c[{j}]={val}', lambda c, j=j, v=val: int(c[j]==v)))

                nf2 = nf + len(extra_feats)
                A_ub2 = np.zeros((len(jdz), nf2))
                A_ub2[:, :nf] = A_ub

                for idx, (u, v) in enumerate(jdz):
                    for k, (_, func) in enumerate(extra_feats):
                        A_ub2[idx, nf+k] = -(func(u) - func(v))

                c_obj2 = np.zeros(nf2)
                bounds2 = [(-100, 100)] * nf2
                result_lp2 = linprog(c_obj2, A_ub=A_ub2, b_ub=b_ub, bounds=bounds2,
                                     method='highs')
                if result_lp2.success:
                    w2 = result_lp2.x
                    print(f"\n  LP FEASIBLE with position-specific features!", flush=True)
                    for j, fname in enumerate(feat_names):
                        if abs(w2[j]) > 0.01:
                            print(f"    {fname}: {w2[j]:.4f}", flush=True)
                    for k, (ename, _) in enumerate(extra_feats):
                        if abs(w2[nf+k]) > 0.01:
                            print(f"    {ename}: {w2[nf+k]:.4f}", flush=True)
                else:
                    print(f"  LP still INFEASIBLE with position-specific features ({nf2} total)",
                          flush=True)

        # === Hard-edge analysis (Δfc<0, Δrank_up>0) ===
        hard_edges = [(u,v) for u,v in jdz
                      if fc(v,n) < fc(u,n) and rank_up.get(v,0) > rank_up.get(u,0)]

        if hard_edges:
            print(f"\n  Hard edges (Δfc<0, Δrank_up>0): {len(hard_edges)}", flush=True)

            # What changes in the config?
            delta_feats = defaultdict(list)
            for u, v in hard_edges:
                fu = compute_features(u, n, rank_up.get(u, 0))
                fv = compute_features(v, n, rank_up.get(v, 0))
                for fname in feat_names:
                    if fname not in ('fc', 'rank_up'):
                        delta_feats[fname].append(fv[fname] - fu[fname])

            print(f"\n  Feature changes on hard edges:", flush=True)
            for fname in feat_names:
                if fname in ('fc', 'rank_up'):
                    continue
                vals = delta_feats[fname]
                if not vals:
                    continue
                mn, mx = min(vals), max(vals)
                mean = sum(vals)/len(vals)
                # Count strictly negative, zero, strictly positive
                neg = sum(1 for v in vals if v < 0)
                zer = sum(1 for v in vals if v == 0)
                pos = sum(1 for v in vals if v > 0)
                if neg == len(vals):
                    marker = " *** ALWAYS NEGATIVE"
                elif pos == len(vals):
                    marker = " *** ALWAYS POSITIVE"
                elif neg + zer == len(vals):
                    marker = " ** NON-POSITIVE"
                elif pos + zer == len(vals):
                    marker = " ** NON-NEGATIVE"
                else:
                    marker = ""
                print(f"    Δ{fname}: [{mn},{mx}] mean={mean:.2f} "
                      f"(neg={neg} zero={zer} pos={pos}){marker}", flush=True)

            # Check: does full_rank - fc - rank_up change on hard edges?
            print(f"\n  Correction = full_rank - fc - rank_up on hard edges:", flush=True)
            corr_changes = []
            for u, v in hard_edges:
                cu = full_rank[u] - fc(u,n) - rank_up.get(u,0)
                cv = full_rank[v] - fc(v,n) - rank_up.get(v,0)
                corr_changes.append(cv - cu)
            neg = sum(1 for v in corr_changes if v < 0)
            zer = sum(1 for v in corr_changes if v == 0)
            pos = sum(1 for v in corr_changes if v > 0)
            print(f"    neg={neg}, zero={zer}, pos={pos}", flush=True)
            if corr_changes:
                print(f"    range: [{min(corr_changes)}, {max(corr_changes)}]", flush=True)

        elapsed = time.time() - t0
        print(f"\n  Time: {elapsed:.1f}s", flush=True)

if __name__ == '__main__':
    main()
