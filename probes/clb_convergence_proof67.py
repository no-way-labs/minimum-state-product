#!/usr/bin/env python3
"""
CONVERGENCE PROOF 67: Per-(int21, intj20) decomposition of jdz
===============================================================
Since jdz edges preserve int(2,1) and int_j(2,0) by definition,
the jdz graph decomposes into independent components indexed by
(int21_val, intj20_val). Test:
1. How many components? Sizes?
2. Is each component a DAG?
3. Max rank per component?
4. Does max rank stay bounded as n grows?
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter, deque

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

def dag_rank(edges, nodes):
    """Compute DAG max rank. Returns (is_dag, max_rank, rank_dist)."""
    adj = defaultdict(list)
    for u, v in edges:
        adj[u].append(v)
    in_deg = defaultdict(int)
    for u, v in edges:
        in_deg[v] += 1
    q = deque([u for u in nodes if in_deg[u] == 0])
    topo = []
    while q:
        node = q.popleft(); topo.append(node)
        for nxt in adj[node]:
            in_deg[nxt] -= 1
            if in_deg[nxt] == 0: q.append(nxt)
    is_dag = len(topo) == len(nodes)
    if not is_dag:
        return False, -1, {}
    rk = {}
    for c in reversed(topo):
        rk[c] = max((rk[s]+1 for s in adj[c]), default=0)
    max_r = max(rk.values()) if rk else 0
    rank_dist = Counter(rk.values())
    return True, max_r, rank_dist

def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 13):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        jdz = list(set((u,v) for u,v in exc_edges
                   if int_21(v,n)-int_21(u,n)==0
                   and int_j_20(v,n)-int_j_20(u,n)==0))

        jdz_nodes = set()
        for u, v in jdz:
            jdz_nodes.add(u); jdz_nodes.add(v)

        print(f"\n{'='*70}", flush=True)
        print(f"n={n}: {len(jdz)} jdz edges, {len(jdz_nodes)} nodes ({time.time()-t0:.1f}s)", flush=True)
        print(f"{'='*70}", flush=True)

        if not jdz: continue

        # Decompose by (int21, intj20) — these are PRESERVED on jdz edges
        comp_edges = defaultdict(list)
        comp_nodes = defaultdict(set)
        for u, v in jdz:
            key = (int_21(u, n), int_j_20(u, n))
            # Verify preservation
            key_v = (int_21(v, n), int_j_20(v, n))
            assert key == key_v, f"NOT PRESERVED: {key} != {key_v}"
            comp_edges[key].append((u, v))
            comp_nodes[key].add(u)
            comp_nodes[key].add(v)

        print(f"  Components: {len(comp_edges)}", flush=True)

        # Analyze each component
        global_max_rank = 0
        all_dag = True
        comp_results = []

        for key in sorted(comp_edges.keys()):
            edges = comp_edges[key]
            nodes = comp_nodes[key]
            is_dag, max_r, rank_dist = dag_rank(edges, nodes)
            comp_results.append((key, len(edges), len(nodes), is_dag, max_r))
            if is_dag:
                global_max_rank = max(global_max_rank, max_r)
            else:
                all_dag = False

        # Summary
        print(f"  All DAG: {all_dag}", flush=True)
        print(f"  Global max rank across components: {global_max_rank}", flush=True)

        # Detailed per-component
        rank_by_comp = Counter()
        for key, ne, nn, is_dag, mr in comp_results:
            rank_by_comp[mr] += 1

        print(f"  Max-rank distribution: {dict(sorted(rank_by_comp.items()))}", flush=True)

        # Show largest components
        comp_results.sort(key=lambda x: -x[1])  # by edge count
        print(f"\n  Largest components:", flush=True)
        for key, ne, nn, is_dag, mr in comp_results[:15]:
            print(f"    (int21={key[0]}, intj20={key[1]}): {ne} edges, {nn} nodes, DAG={is_dag}, rank={mr}", flush=True)

        # Also: fc distribution WITHIN each component
        if n <= 10:
            print(f"\n  fc spread within components:", flush=True)
            for key, ne, nn, is_dag, mr in comp_results[:10]:
                nodes = comp_nodes[key]
                fcs = [sum(1 for j in range(n) if c[j] != c[(j+1)%n]) for c in nodes]
                fc_range = (min(fcs), max(fcs))
                print(f"    (int21={key[0]}, intj20={key[1]}): fc range {fc_range}, spread={fc_range[1]-fc_range[0]}", flush=True)

        # Also: Δfc within components
        print(f"\n  Δfc within components:", flush=True)
        for key, ne, nn, is_dag, mr in comp_results[:10]:
            edges = comp_edges[key]
            dfcs = []
            for u, v in edges:
                fc_u = sum(1 for j in range(n) if u[j] != u[(j+1)%n])
                fc_v = sum(1 for j in range(n) if v[j] != v[(j+1)%n])
                dfcs.append(fc_v - fc_u)
            dfc_dist = Counter(dfcs)
            print(f"    (int21={key[0]}, intj20={key[1]}): Δfc={dict(sorted(dfc_dist.items()))}", flush=True)

        elapsed = time.time() - t0
        print(f"\n  Total time: {elapsed:.1f}s", flush=True)

if __name__ == '__main__':
    main()
