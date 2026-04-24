#!/usr/bin/env python3
"""
CONVERGENCE PROOF 66: Contraction-based induction for jdz DAG
=============================================================
Idea: If two adjacent interior positions have the same value (a "run"),
we can contract them. If the contraction preserves jdz edge structure,
then DAG(n) implies DAG(n+1).

Tests:
1. Do all jdz configs have an interior run? (prerequisite for contraction)
2. Does contraction map jdz edges to jdz edges?
3. What's the minimum # of interior runs in jdz configs?

Also: test PROJECTION approach (delete one position + remap).
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter

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

def interior_runs(c, n):
    """Find positions j in interior where c[j]=c[j+1] (both interior)."""
    runs = []
    for j in range(2, n-3):  # j and j+1 both in [2, n-3]
        if c[j] == c[j+1]:
            runs.append(j)
    return runs

def contract(c, k, n):
    """Contract: remove position k+1 from config c of length n."""
    return tuple(c[j] for j in range(n) if j != k+1)

def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        jdz = list(set((u,v) for u,v in exc_edges
                   if int_21(v,n)-int_21(u,n)==0
                   and int_j_20(v,n)-int_j_20(u,n)==0))

        # Collect all jdz nodes
        jdz_nodes = set()
        for u, v in jdz:
            jdz_nodes.add(u); jdz_nodes.add(v)

        print(f"\n{'='*60}", flush=True)
        print(f"n={n}: {len(jdz)} jdz edges, {len(jdz_nodes)} nodes ({time.time()-t0:.1f}s)", flush=True)
        print(f"{'='*60}", flush=True)

        if not jdz: continue

        # === 1. Interior runs in jdz nodes ===
        run_counts = Counter()
        no_run_configs = []
        for c in jdz_nodes:
            runs = interior_runs(c, n)
            run_counts[len(runs)] += 1
            if len(runs) == 0:
                no_run_configs.append(c)

        print(f"  Interior run counts: {dict(sorted(run_counts.items()))}", flush=True)
        print(f"  Configs with NO interior run: {len(no_run_configs)}/{len(jdz_nodes)}", flush=True)
        if no_run_configs and len(no_run_configs) <= 10:
            for c in no_run_configs[:5]:
                print(f"    {c}", flush=True)

        # === 2. For configs WITH interior runs: does contraction map to jdz system? ===
        if n >= 7:  # Need n-1 ≥ 6 for contraction to make sense
            # Build jdz for n-1
            exc_edges_prev, ms_prev = build_excursion_graph(n-1)
            jdz_prev = set((u,v) for u,v in exc_edges_prev
                       if int_21(v,n-1)-int_21(u,n-1)==0
                       and int_j_20(v,n-1)-int_j_20(u,n-1)==0)
            jdz_nodes_prev = set()
            for u, v in jdz_prev:
                jdz_nodes_prev.add(u); jdz_nodes_prev.add(v)

            # For each jdz edge with SHARED interior run, check contraction
            n_contractible = 0
            n_edge_maps = 0
            n_edge_not_maps = 0
            n_node_maps = 0
            n_node_not_maps = 0

            for u, v in jdz:
                # Find shared interior runs (both u and v have run at same position)
                u_runs = set(interior_runs(u, n))
                v_runs = set(interior_runs(v, n))
                shared = u_runs & v_runs

                if not shared: continue
                n_contractible += 1

                # Try the first shared run position
                k = min(shared)
                cu = contract(u, k, n)
                cv = contract(v, k, n)

                # Check if cu, cv are in jdz(n-1)
                cu_in = cu in jdz_nodes_prev
                cv_in = cv in jdz_nodes_prev
                if cu_in and cv_in:
                    n_node_maps += 1
                else:
                    n_node_not_maps += 1

                # Check if (cu, cv) is a jdz edge in n-1
                if (cu, cv) in jdz_prev:
                    n_edge_maps += 1
                else:
                    n_edge_not_maps += 1

            print(f"\n  Contraction analysis (n={n} → n-1={n-1}):", flush=True)
            print(f"    Edges with shared interior run: {n_contractible}/{len(jdz)}", flush=True)
            print(f"    Both nodes map to jdz(n-1): {n_node_maps}/{n_contractible}", flush=True)
            print(f"    Edge maps to jdz edge: {n_edge_maps}/{n_contractible}", flush=True)

        # === 3. fc distribution of jdz nodes ===
        fc_dist = Counter()
        for c in jdz_nodes:
            fc = sum(1 for j in range(n) if c[j] != c[(j+1)%n])
            fc_dist[fc] += 1
        print(f"\n  fc distribution: {dict(sorted(fc_dist.items()))}", flush=True)

        # === 4. For edges WITHOUT shared interior run: what do they look like? ===
        no_shared = []
        for u, v in jdz:
            u_runs = set(interior_runs(u, n))
            v_runs = set(interior_runs(v, n))
            if not (u_runs & v_runs):
                no_shared.append((u, v))
        print(f"  Edges with NO shared interior run: {len(no_shared)}/{len(jdz)}", flush=True)
        if no_shared and len(no_shared) <= 20:
            for u, v in no_shared[:5]:
                print(f"    {u} -> {v}", flush=True)
                print(f"      u_runs={interior_runs(u,n)}, v_runs={interior_runs(v,n)}", flush=True)

        # === 5. Per-fc-level analysis: is each fc level independently DAG? ===
        from collections import deque
        by_fc = defaultdict(list)
        for u, v in jdz:
            fc_u = sum(1 for j in range(n) if u[j] != u[(j+1)%n])
            by_fc[fc_u].append((u, v))

        print(f"\n  Per-fc-level DAG:", flush=True)
        for fc_val in sorted(by_fc.keys()):
            edges = by_fc[fc_val]
            adj = defaultdict(list)
            nodes = set()
            for u, v in edges:
                adj[u].append(v); nodes.add(u); nodes.add(v)
            in_deg = defaultdict(int)
            for u, v in edges: in_deg[v] += 1
            q = deque([u for u in nodes if in_deg[u] == 0])
            cnt = 0
            rk = {}
            while q:
                node = q.popleft(); cnt += 1; rk[node] = 0
                for nxt in adj[node]:
                    in_deg[nxt] -= 1
                    if in_deg[nxt] == 0: q.append(nxt)
            max_r = 0
            if cnt == len(nodes):
                for c in reversed(list(rk.keys())):
                    rk[c] = max((rk.get(s,0)+1 for s in adj[c]), default=0)
                max_r = max(rk.values()) if rk else 0
            is_dag = cnt == len(nodes)
            print(f"    fc={fc_val}: {len(edges)} edges, {len(nodes)} nodes, DAG={is_dag}, max_rank={max_r}", flush=True)

if __name__ == '__main__':
    main()
