#!/usr/bin/env python3
"""
CONVERGENCE PROOF 74: Decompose the full DAG rank of jdz
=========================================================
Since jdz IS a DAG (verified), it has a well-defined rank function.
Question: can this rank be expressed as fc_max - fc + rank_up + correction?
What is the correction? Is it a function of boundary + local structure?

Also: test whether the full rank correlates with any simple quantity
that could be proved monotone analytically.
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
            L = c[(i - 1) % n_val]
            S = c[i]
            R = c[(i + 1) % n_val]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c)
                lst[i] = out
                succ = tuple(lst)
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
        visited = {b}
        queue = [b]
        head = 0
        while head < len(queue):
            node = queue[head]
            head += 1
            if node in anom_sources:
                for src in anom_target_map.get(b, []):
                    exc_edges.add((src, node))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append(nxt)
    return list(exc_edges), ms

def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def int_j_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        jdz = list(set((u, v) for u, v in exc_edges
                       if int_21(v, n) - int_21(u, n) == 0
                       and int_j_20(v, n) - int_j_20(u, n) == 0))

        if not jdz:
            print(f"n={n}: no jdz edges")
            continue

        # Build full jdz adjacency
        jdz_adj = defaultdict(list)
        jdz_nodes = set()
        for u, v in jdz:
            jdz_adj[u].append(v)
            jdz_nodes.add(u)
            jdz_nodes.add(v)

        # Build Δfc≥0 subgraph
        up_adj = defaultdict(list)
        up_nodes = set()
        for u, v in jdz:
            if fc(v, n) >= fc(u, n):
                up_adj[u].append(v)
                up_nodes.add(u)
                up_nodes.add(v)

        # Compute rank_up (rank in Δfc≥0 subgraph)
        in_deg_up = defaultdict(int)
        for u in up_nodes:
            for v in up_adj[u]:
                in_deg_up[v] += 1
        q = deque([u for u in up_nodes if in_deg_up[u] == 0])
        topo_up = []
        while q:
            node = q.popleft()
            topo_up.append(node)
            for nxt in up_adj[node]:
                in_deg_up[nxt] -= 1
                if in_deg_up[nxt] == 0:
                    q.append(nxt)
        assert len(topo_up) == len(up_nodes)

        rank_up = {}
        for c in reversed(topo_up):
            rank_up[c] = max((rank_up[s] + 1 for s in up_adj[c]), default=0)

        # Compute full DAG rank of jdz
        in_deg = defaultdict(int)
        for u, v in jdz:
            in_deg[v] += 1
        q = deque([u for u in jdz_nodes if in_deg[u] == 0])
        topo = []
        while q:
            node = q.popleft()
            topo.append(node)
            for nxt in jdz_adj[node]:
                in_deg[nxt] -= 1
                if in_deg[nxt] == 0:
                    q.append(nxt)
        assert len(topo) == len(jdz_nodes), f"jdz NOT DAG at n={n}!"

        full_rank = {}
        for c in reversed(topo):
            full_rank[c] = max((full_rank[s] + 1 for s in jdz_adj[c]), default=0)
        max_full_rank = max(full_rank.values())

        # Group by (int21, intj20) component
        comp = defaultdict(set)
        for c in jdz_nodes:
            comp[(int_21(c, n), int_j_20(c, n))].add(c)

        print(f"\n{'=' * 70}", flush=True)
        print(f"n={n}: {len(jdz)} jdz edges, full DAG rank={max_full_rank} ({time.time()-t0:.1f}s)", flush=True)
        print(f"{'=' * 70}", flush=True)

        # For the dominant component, analyze rank structure
        dom_key = max(comp.keys(), key=lambda k: len(comp[k]))
        dom_nodes = comp[dom_key]
        dom_edges = [(u, v) for u, v in jdz if u in dom_nodes]

        # fc range within dominant component
        fc_vals = [fc(c, n) for c in dom_nodes]
        fc_min, fc_max = min(fc_vals), max(fc_vals)
        print(f"\n  Dominant component {dom_key}: {len(dom_nodes)} nodes, {len(dom_edges)} edges", flush=True)
        print(f"  fc range: [{fc_min}, {fc_max}], range = {fc_max - fc_min}", flush=True)

        # Check: full_rank vs various formulas
        # Formula 1: full_rank = fc_max - fc + rank_up
        residuals = []
        for c in dom_nodes:
            predicted = (fc_max - fc(c, n)) + rank_up.get(c, 0)
            actual = full_rank[c]
            residuals.append(actual - predicted)

        r_min, r_max = min(residuals), max(residuals)
        r_mean = sum(residuals) / len(residuals)
        print(f"\n  Formula: full_rank = (fc_max - fc) + rank_up", flush=True)
        print(f"  Residual range: [{r_min}, {r_max}], mean={r_mean:.2f}", flush=True)

        # Distribution of residuals
        res_dist = Counter(residuals)
        print(f"  Residual distribution: {dict(sorted(res_dist.items()))}", flush=True)

        # Is residual a function of boundary?
        bdry_residuals = defaultdict(set)
        for c in dom_nodes:
            bdry = (c[0], c[1], c[n-2], c[n-1])
            predicted = (fc_max - fc(c, n)) + rank_up.get(c, 0)
            actual = full_rank[c]
            bdry_residuals[bdry].add(actual - predicted)

        all_single = all(len(v) == 1 for v in bdry_residuals.values())
        print(f"\n  Is residual a function of boundary alone? {all_single}", flush=True)
        if not all_single:
            # Show boundaries with multiple residual values
            multi = {k: v for k, v in bdry_residuals.items() if len(v) > 1}
            print(f"  Boundaries with multiple residuals: {len(multi)}", flush=True)
            for bdry, vals in sorted(multi.items(), key=lambda x: -len(x[1]))[:10]:
                print(f"    {bdry}: residuals = {sorted(vals)}", flush=True)

        # Is residual a function of (boundary, fc)?
        bf_residuals = defaultdict(set)
        for c in dom_nodes:
            bdry = (c[0], c[1], c[n-2], c[n-1])
            f = fc(c, n)
            predicted = (fc_max - f) + rank_up.get(c, 0)
            actual = full_rank[c]
            bf_residuals[(bdry, f)].add(actual - predicted)
        all_single_bf = all(len(v) == 1 for v in bf_residuals.values())
        print(f"  Is residual a function of (boundary, fc)? {all_single_bf}", flush=True)

        # More formulas: try full_rank = a*fc + b*rank_up + c for optimal a,b,c
        # Use least squares on dominant component
        if len(dom_nodes) >= 10:
            # Collect data
            X = []
            Y = []
            for c in dom_nodes:
                X.append((fc(c, n), rank_up.get(c, 0), 1))
                Y.append(full_rank[c])

            # Simple: compute correlation of full_rank with various quantities
            features = {
                'fc': [fc(c, n) for c in dom_nodes],
                'rank_up': [rank_up.get(c, 0) for c in dom_nodes],
                'fc_max-fc': [fc_max - fc(c, n) for c in dom_nodes],
                '(fc_max-fc)+rank_up': [(fc_max - fc(c, n)) + rank_up.get(c, 0) for c in dom_nodes],
                '(fc_max-fc)+3*rank_up': [(fc_max - fc(c, n)) + 3*rank_up.get(c, 0) for c in dom_nodes],
            }

            ys = [full_rank[c] for c in dom_nodes]
            y_mean = sum(ys) / len(ys)
            ss_tot = sum((y - y_mean)**2 for y in ys)

            print(f"\n  Correlation with full_rank (R²):", flush=True)
            for fname, fvals in features.items():
                f_mean = sum(fvals) / len(fvals)
                if ss_tot == 0:
                    r2 = 1.0
                else:
                    # Simple linear regression
                    ss_xy = sum((f - f_mean) * (y - y_mean) for f, y in zip(fvals, ys))
                    ss_xx = sum((f - f_mean)**2 for f in fvals)
                    if ss_xx == 0:
                        r2 = 0.0
                    else:
                        b1 = ss_xy / ss_xx
                        b0 = y_mean - b1 * f_mean
                        ss_res = sum((y - (b0 + b1 * f))**2 for f, y in zip(fvals, ys))
                        r2 = 1 - ss_res / ss_tot
                print(f"    {fname:30s}: R² = {r2:.6f}", flush=True)

        # === KEY: Check if full_rank is uniquely determined by (fc, rank_up, boundary) ===
        det_key = defaultdict(set)
        for c in dom_nodes:
            key = (fc(c, n), rank_up.get(c, 0), c[0], c[1], c[n-2], c[n-1])
            det_key[key].add(full_rank[c])
        all_det = all(len(v) == 1 for v in det_key.values())
        multi_det = sum(1 for v in det_key.values() if len(v) > 1)
        print(f"\n  full_rank determined by (fc, rank_up, boundary)? {all_det}", flush=True)
        if not all_det:
            print(f"  Keys with multiple ranks: {multi_det}/{len(det_key)}", flush=True)
            # Show examples
            for key, vals in sorted(det_key.items(), key=lambda x: -len(x[1]))[:5]:
                f, r, p0, p1, pn2, pn1 = key
                print(f"    fc={f}, rank_up={r}, bdry=({p0},{p1},{pn2},{pn1}): "
                      f"full_ranks = {sorted(vals)}", flush=True)

        # === What quantity DOES distinguish nodes with same (fc, rank_up, boundary)? ===
        # Try: number of positions with value 2, positions of (2,1) pairs, etc.
        if not all_det:
            # For one of the multi-rank keys, compare the configs
            for key, vals in sorted(det_key.items(), key=lambda x: -len(x[1]))[:3]:
                f, r, p0, p1, pn2, pn1 = key
                configs_by_rank = defaultdict(list)
                for c in dom_nodes:
                    k2 = (fc(c, n), rank_up.get(c, 0), c[0], c[1], c[n-2], c[n-1])
                    if k2 == key:
                        configs_by_rank[full_rank[c]].append(c)

                print(f"\n  Configs at fc={f}, rank_up={r}, bdry=({p0},{p1},{pn2},{pn1}):", flush=True)
                for rank_val in sorted(configs_by_rank.keys()):
                    cfgs = configs_by_rank[rank_val]
                    # Interior summary
                    for c in cfgs[:2]:
                        interior = c[2:n-2]
                        pos_21 = [j for j in range(2, n-2) if c[j]==2 and c[j+1]==1]
                        pos_20 = [j for j in range(2, n-2) if c[j]==2 and c[j+1]==0]
                        n2 = sum(1 for x in interior if x == 2)
                        print(f"    rank={rank_val}: {c} int={interior} "
                              f"#2={n2} pos21={pos_21} pos20={pos_20}", flush=True)

        # === Also check: positions of (2,1) pairs ===
        # If int_21 = k, the positions form a set of size k. Does the "leftmost" position correlate?
        if int_21(list(dom_nodes)[0], n) >= 1:
            leftmost_21 = {}
            for c in dom_nodes:
                for j in range(2, n-2):
                    if c[j] == 2 and c[j+1] == 1:
                        leftmost_21[c] = j
                        break
                else:
                    leftmost_21[c] = n  # no (2,1) pair

            det_key2 = defaultdict(set)
            for c in dom_nodes:
                key = (fc(c, n), rank_up.get(c, 0), c[0], c[1], c[n-2], c[n-1], leftmost_21[c])
                det_key2[key].add(full_rank[c])
            all_det2 = all(len(v) == 1 for v in det_key2.values())
            multi_det2 = sum(1 for v in det_key2.values() if len(v) > 1)
            print(f"\n  Adding leftmost_21: determined? {all_det2} ({multi_det2} ambiguous)", flush=True)

        elapsed = time.time() - t0
        print(f"\n  Time: {elapsed:.1f}s", flush=True)

if __name__ == '__main__':
    main()
