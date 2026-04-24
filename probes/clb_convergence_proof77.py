#!/usr/bin/env python3
"""
CONVERGENCE PROOF 77: Precise dead-end analysis + cycle reachability in jdz
============================================================================
Cross-reference proof76 findings with the actual jdz graph.

Key questions:
1. Do rank-3 endpoint configs (in Δfc≥0 subgraph) have ANY outgoing jdz edges?
2. Which (0,2,2,1) configs are true dead ends vs have outgoing edges?
3. Can any path from (0,2,2,1) reach back to (0,2,2,1)?
4. What is the fc signature along such paths?
5. Is there a potential that works within each sub-component?
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
    """Build the complete jdz graph and supporting structures."""
    ms, fs = build_system(n_val)
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)
    n = n_val

    # Build raw excursion edges
    anom_edges = []
    dfc_le0_adj = defaultdict(list)
    for c in bad_list:
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
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

    # Filter to jdz edges
    jdz = []
    for u, v in exc_edges:
        if (int_21(v, n) - int_21(u, n) == 0 and
            int_j_20(v, n) - int_j_20(u, n) == 0):
            jdz.append((u, v))

    return jdz, ms, fs, bad_set


def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 12):
        t0 = time.time()
        jdz, ms, fs, bad_set = build_jdz_graph(n_val)
        n = n_val

        if not jdz:
            print(f"n={n}: no jdz edges")
            continue

        # Build adjacency
        jdz_adj = defaultdict(list)
        jdz_nodes = set()
        for u, v in jdz:
            jdz_adj[u].append(v)
            jdz_nodes.add(u)
            jdz_nodes.add(v)

        # Build Δfc≥0 subgraph and compute rank_up
        up_adj = defaultdict(list)
        up_nodes = set()
        for u, v in jdz:
            if fc(v, n) >= fc(u, n):
                up_adj[u].append(v)
                up_nodes.add(u)
                up_nodes.add(v)

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
        assert len(topo_up) == len(up_nodes), f"Δfc≥0 not DAG at n={n}!"

        rank_up = {}
        for c in reversed(topo_up):
            rank_up[c] = max((rank_up[s] + 1 for s in up_adj[c]), default=0)
        max_rank_up = max(rank_up.values()) if rank_up else 0

        print(f"\n{'=' * 70}", flush=True)
        print(f"n={n}: {len(jdz)} jdz edges, max rank_up={max_rank_up} ({time.time()-t0:.1f}s)", flush=True)

        # === 1. Identify rank-3 endpoints ===
        rank3_endpoints = set()
        for c in up_nodes:
            if rank_up[c] == 0 and any(rank_up.get(u, -1) >= 2 for u in up_nodes
                                        if c in up_adj.get(u, [])):
                # c has rank_up=0 and is reachable from rank_up≥2 via up edges
                rank3_endpoints.add(c)

        # Alternative: endpoints of rank-3 paths (rank_up=0 nodes reachable from rank_up=3)
        # Find all rank_up=0 nodes that can be reached from rank_up=3 nodes
        # via Δfc≥0 edges
        rank3_sources = {c for c in up_nodes if rank_up[c] == max_rank_up}
        # BFS from rank-3 sources through Δfc≥0 edges
        reachable_from_r3 = set()
        queue = list(rank3_sources)
        visited = set(queue)
        head = 0
        while head < len(queue):
            node = queue[head]
            head += 1
            for nxt in up_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append(nxt)
        rank3_endpoints = {c for c in visited if rank_up.get(c, -1) == 0}

        # Boundary distribution of rank-3 endpoints
        r3_bdry = Counter()
        for c in rank3_endpoints:
            r3_bdry[(c[0], c[1], c[n-2], c[n-1])] += 1
        print(f"\n  Rank-{max_rank_up} sources: {len(rank3_sources)}", flush=True)
        print(f"  Rank-0 endpoints reachable from rank-{max_rank_up}: {len(rank3_endpoints)}", flush=True)
        print(f"  Boundary distribution of endpoints:", flush=True)
        for bdry, cnt in r3_bdry.most_common(5):
            print(f"    {bdry}: {cnt}", flush=True)

        # === 2. Do rank-3 endpoints have outgoing jdz edges? ===
        r3_out = 0
        r3_out_details = []
        for c in rank3_endpoints:
            if jdz_adj.get(c):
                r3_out += 1
                for v in jdz_adj[c]:
                    dfc = fc(v, n) - fc(c, n)
                    r3_out_details.append((c, v, dfc))

        print(f"\n  Rank-{max_rank_up} endpoints with outgoing jdz edges: {r3_out}/{len(rank3_endpoints)}", flush=True)
        if r3_out > 0:
            print(f"  Total outgoing edges from endpoints: {len(r3_out_details)}", flush=True)
            dfc_dist = Counter(d for _, _, d in r3_out_details)
            print(f"  Δfc distribution: {dict(sorted(dfc_dist.items()))}", flush=True)
            for c, v, dfc in r3_out_details[:5]:
                print(f"    {c[:4]}...{c[-2:]} → {v[:4]}...{v[-2:]}: Δfc={dfc}", flush=True)

        # === 3. ALL (0,2,2,1) configs: dead ends vs live ===
        bdry_0221 = [c for c in jdz_nodes if c[0]==0 and c[1]==2 and c[n-2]==2 and c[n-1]==1]
        dead_0221 = [c for c in bdry_0221 if not jdz_adj.get(c)]
        live_0221 = [c for c in bdry_0221 if jdz_adj.get(c)]

        print(f"\n  Boundary (0,2,2,1) in jdz: {len(bdry_0221)} nodes", flush=True)
        print(f"    Dead ends (0 outgoing): {len(dead_0221)}", flush=True)
        print(f"    Live (has outgoing): {len(live_0221)}", flush=True)

        if live_0221:
            # What distinguishes live from dead?
            live_interiors = Counter()
            dead_interiors = Counter()
            for c in live_0221:
                live_interiors[(c[2], c[3])] += 1
            for c in dead_0221:
                dead_interiors[(c[2], c[3])] += 1
            print(f"    Live c[2],c[3] distribution: {dict(live_interiors)}", flush=True)
            print(f"    Dead c[2],c[3] distribution: {dict(dead_interiors)}", flush=True)

        # === 4. Path reachability: (0,2,2,1) → ... → (0,2,2,1) ===
        # BFS from all (0,2,2,1) configs, check if any reach another (0,2,2,1) config
        bdry_0221_set = set(bdry_0221)
        reached_0221 = set()
        for start in bdry_0221:
            # BFS avoiding start itself
            vis = {start}
            q = [start]
            head = 0
            while head < len(q):
                node = q[head]
                head += 1
                for nxt in jdz_adj.get(node, []):
                    if nxt not in vis:
                        vis.add(nxt)
                        q.append(nxt)
                        if nxt in bdry_0221_set and nxt != start:
                            reached_0221.add((start, nxt))

        print(f"\n  Paths (0,2,2,1) → ... → (0,2,2,1): {len(reached_0221)}", flush=True)
        if reached_0221:
            for u, v in list(reached_0221)[:5]:
                dfc = fc(v, n) - fc(u, n)
                print(f"    {u} → {v}: Δfc={dfc}", flush=True)

        # === 5. Full jdz DAG rank per boundary class ===
        # Compute full DAG rank
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

        # For (0,2,2,1) configs: full_rank distribution
        if bdry_0221:
            r_vals = [full_rank[c] for c in bdry_0221]
            print(f"\n  Full DAG rank of (0,2,2,1) configs: max={max(r_vals)}, "
                  f"min={min(r_vals)}, mean={sum(r_vals)/len(r_vals):.1f}", flush=True)

            # Dead vs live rank distributions
            if dead_0221:
                d_ranks = [full_rank[c] for c in dead_0221]
                print(f"    Dead end ranks: {Counter(d_ranks).most_common(5)}", flush=True)
            if live_0221:
                l_ranks = [full_rank[c] for c in live_0221]
                print(f"    Live ranks: {Counter(l_ranks).most_common(5)}", flush=True)

        # === 6. fc-indexed DAG structure ===
        # Key test: is there a monotone function of (fc, boundary) that decreases on ALL jdz edges?
        # Within each (int21, intj20) component, check if lexicographic (fc, boundary_weight) works
        bdry_weight_tests = {
            'P0+P1+Pn2+Pn1': lambda c: c[0] + c[1] + c[n-2] + c[n-1],
            '3*P0+2*P1+Pn2': lambda c: 3*c[0] + 2*c[1] + c[n-2],
            'P1+2*Pn2+3*Pn1': lambda c: c[1] + 2*c[n-2] + 3*c[n-1],
        }

        print(f"\n  Lexicographic (fc, bdry_weight) tests on all jdz edges:", flush=True)
        for tname, tfunc in bdry_weight_tests.items():
            # Test: (fc, weight) strictly decreasing in lex order
            # i.e., fc(v) < fc(u), OR (fc(v)==fc(u) AND weight(v) < weight(u))
            viol = 0
            for u, v in jdz:
                fu, fv = fc(u, n), fc(v, n)
                wu, wv = tfunc(u), tfunc(v)
                if not (fv < fu or (fv == fu and wv < wu)):
                    viol += 1
            pct = 100 * viol / len(jdz)
            print(f"    (-fc, -{tname}): {viol}/{len(jdz)} violations ({pct:.1f}%)", flush=True)

        # === 7. CRITICAL: Is there a quantity that strictly decreases on EVERY jdz edge? ===
        # Test multi-dimensional: (int_j_21, fc, ...)
        # Since int_j_21 is preserved, this reduces to testing fc within each sub-component
        # But fc can increase. So test: (-fc, -something_else)
        # Count #configs with each interior value
        def interior_sum(c, n):
            return sum(c[j] for j in range(2, n - 2))

        def interior_weighted(c, n):
            return sum(j * c[j] for j in range(2, n - 2))

        def n_twos(c, n):
            return sum(1 for j in range(2, n - 2) if c[j] == 2)

        def n_zeros(c, n):
            return sum(1 for j in range(2, n - 2) if c[j] == 0)

        multi_tests = {
            'interior_sum': interior_sum,
            'interior_weighted': interior_weighted,
            '#twos_interior': n_twos,
            '#zeros_interior': n_zeros,
        }

        print(f"\n  Additional monotonicity tests:", flush=True)
        for tname, tfunc in multi_tests.items():
            for sign in [1, -1]:
                s = '+' if sign > 0 else '-'
                viol = 0
                for u, v in jdz:
                    if sign * tfunc(v, n) >= sign * tfunc(u, n):
                        viol += 1
                pct = 100 * viol / len(jdz)
                if pct < 30:
                    print(f"    {s}{tname}: {viol}/{len(jdz)} violations ({pct:.1f}%)", flush=True)

        # === 8. DEEP: On Δfc≥0 jdz edges, what changes in the interior? ===
        print(f"\n  Interior changes on Δfc≥0 jdz edges:", flush=True)
        pos_changes = Counter()
        for u, v in jdz:
            if fc(v, n) >= fc(u, n):
                changed = tuple(j for j in range(n) if u[j] != v[j])
                for j in changed:
                    pos_changes[(j, u[j], v[j])] += 1
        for (j, old, new), cnt in pos_changes.most_common(15):
            pos_type = ('bot' if j == 0 else 'low' if j == 1 else
                       'high' if j == n-2 else 'top' if j == n-1 else f'mid[{j}]')
            print(f"    {pos_type}: {old}→{new}: {cnt}", flush=True)

        elapsed = time.time() - t0
        print(f"\n  Total time: {elapsed:.1f}s", flush=True)

if __name__ == '__main__':
    main()
