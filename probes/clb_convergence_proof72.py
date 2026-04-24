#!/usr/bin/env python3
"""
CONVERGENCE PROOF 72: Boundary automaton for Δfc≥0 jdz paths
=============================================================
The boundary 4-tuple (P0, P1, P(n-2), P(n-1)) evolves as Δfc≥0 steps
are taken. Build the boundary transition graph:
  - Nodes: observed boundary 4-tuples
  - Edges: observed transitions
If this graph is a DAG with rank ≤ 3 → explains the rank bound.
Also: is the boundary transition INDEPENDENT of n?
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

def bdry(c, n):
    return (c[0], c[1], c[n - 2], c[n - 1])

def main():
    sys.stdout.reconfigure(line_buffering=True)

    # Collect boundary transitions across all n
    all_bdry_edges = set()
    all_bdry_nodes = set()

    for n_val in range(5, 13):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        jdz = list(set((u, v) for u, v in exc_edges
                       if int_21(v, n) - int_21(u, n) == 0
                       and int_j_20(v, n) - int_j_20(u, n) == 0))

        if not jdz:
            print(f"n={n}: no jdz edges")
            continue

        # Δfc≥0 edges
        up_edges = [(u, v) for u, v in jdz if fc(v, n) >= fc(u, n)]

        # Build boundary transition graph for this n
        n_bdry_edges = set()
        n_bdry_nodes = set()
        bdry_edge_count = Counter()

        for u, v in up_edges:
            bu = bdry(u, n)
            bv = bdry(v, n)
            n_bdry_edges.add((bu, bv))
            n_bdry_nodes.add(bu)
            n_bdry_nodes.add(bv)
            bdry_edge_count[(bu, bv)] += 1
            all_bdry_edges.add((bu, bv))
            all_bdry_nodes.add(bu)
            all_bdry_nodes.add(bv)

        # Check if boundary graph is DAG
        adj = defaultdict(list)
        for bu, bv in n_bdry_edges:
            adj[bu].append(bv)
        in_deg = defaultdict(int)
        for bu, bv in n_bdry_edges:
            in_deg[bv] += 1
        q = deque([u for u in n_bdry_nodes if in_deg[u] == 0])
        topo = []
        while q:
            node = q.popleft()
            topo.append(node)
            for nxt in adj[node]:
                in_deg[nxt] -= 1
                if in_deg[nxt] == 0:
                    q.append(nxt)
        is_dag = len(topo) == len(n_bdry_nodes)

        if is_dag:
            rk = {}
            for c in reversed(topo):
                rk[c] = max((rk[s] + 1 for s in adj[c]), default=0)
            max_r = max(rk.values()) if rk else 0
        else:
            max_r = -1

        print(f"n={n}: {len(up_edges)} Δfc≥0 edges → {len(n_bdry_edges)} boundary edges, "
              f"{len(n_bdry_nodes)} boundary nodes, DAG={is_dag}, rank={max_r} ({time.time()-t0:.1f}s)", flush=True)

        if is_dag and n_val <= 11:
            # Show boundary graph
            print(f"  Boundary nodes by rank:", flush=True)
            for r in range(max_r + 1):
                nodes_at_r = [c for c in n_bdry_nodes if rk.get(c) == r]
                print(f"    rank={r}: {nodes_at_r}", flush=True)

            # Show edges
            print(f"  Boundary edges (top by count):", flush=True)
            for (bu, bv), cnt in bdry_edge_count.most_common(20):
                print(f"    {bu} → {bv}: {cnt}", flush=True)

    # === Global boundary graph (union of all n) ===
    print(f"\n{'=' * 70}", flush=True)
    print(f"GLOBAL boundary graph (union n=5..12):", flush=True)
    print(f"  {len(all_bdry_edges)} edges, {len(all_bdry_nodes)} nodes", flush=True)

    adj = defaultdict(list)
    for bu, bv in all_bdry_edges:
        adj[bu].append(bv)
    in_deg = defaultdict(int)
    for bu, bv in all_bdry_edges:
        in_deg[bv] += 1
    q = deque([u for u in all_bdry_nodes if in_deg[u] == 0])
    topo = []
    while q:
        node = q.popleft()
        topo.append(node)
        for nxt in adj[node]:
            in_deg[nxt] -= 1
            if in_deg[nxt] == 0:
                q.append(nxt)
    is_dag = len(topo) == len(all_bdry_nodes)

    if is_dag:
        rk = {}
        for c in reversed(topo):
            rk[c] = max((rk[s] + 1 for s in adj[c]), default=0)
        max_r = max(rk.values()) if rk else 0
        print(f"  DAG: {is_dag}, max rank: {max_r}", flush=True)

        for r in range(max_r + 1):
            nodes_at_r = sorted([c for c in all_bdry_nodes if rk.get(c) == r])
            print(f"  Rank {r}: {nodes_at_r}", flush=True)

        print(f"\n  All edges:", flush=True)
        for bu in sorted(all_bdry_nodes, key=lambda x: -rk.get(x, 0)):
            for bv in sorted(set(adj[bu])):
                print(f"    {bu} (r={rk[bu]}) → {bv} (r={rk[bv]})", flush=True)
    else:
        print(f"  NOT A DAG! ({len(topo)}/{len(all_bdry_nodes)})", flush=True)
        # Find cycle
        remaining = all_bdry_nodes - set(topo)
        print(f"  Nodes in cycle(s): {remaining}", flush=True)

    # === Also check: do self-loops exist in boundary? ===
    self_loops = [(bu, bv) for bu, bv in all_bdry_edges if bu == bv]
    print(f"\n  Self-loops: {len(self_loops)}", flush=True)
    for bu, bv in self_loops:
        print(f"    {bu}", flush=True)

if __name__ == '__main__':
    main()
