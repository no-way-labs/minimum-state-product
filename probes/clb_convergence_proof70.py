#!/usr/bin/env python3
"""
CONVERGENCE PROOF 70: Anatomy of Δfc≥0 paths in jdz
=====================================================
The Δfc≥0 subgraph has rank ≤ 3 (verified n=5..11). WHY?
Examine:
1. All paths of length 2-3 in the Δfc≥0 subgraph
2. Which anomalous entries appear at each step
3. What constrains the 4th step (why can't paths be length 4)?
4. Position types and fc changes along these paths
5. Max total fc gain along Δfc≥0 paths

Also: check if the rank bound might actually be 3 for ALL n,
or if it could increase to 4 at larger n.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter, deque

def delta_fc_val(L, S, R, out):
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

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])

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

        # Build adjacency for jdz
        jdz_adj = defaultdict(list)
        jdz_nodes = set()
        for u, v in jdz:
            jdz_adj[u].append(v)
            jdz_nodes.add(u)
            jdz_nodes.add(v)

        # Δfc≥0 subgraph
        up_adj = defaultdict(list)
        up_nodes = set()
        for u, v in jdz:
            if fc(v, n) >= fc(u, n):
                up_adj[u].append(v)
                up_nodes.add(u)
                up_nodes.add(v)

        # Compute rank in Δfc≥0 subgraph
        # First, topological sort
        in_deg = defaultdict(int)
        for u in up_nodes:
            for v in up_adj[u]:
                in_deg[v] += 1
        q = deque([u for u in up_nodes if in_deg[u] == 0])
        topo = []
        while q:
            node = q.popleft()
            topo.append(node)
            for nxt in up_adj[node]:
                in_deg[nxt] -= 1
                if in_deg[nxt] == 0:
                    q.append(nxt)
        assert len(topo) == len(up_nodes), "Δfc≥0 subgraph not DAG!"

        rank_up = {}
        for c in reversed(topo):
            rank_up[c] = max((rank_up[s] + 1 for s in up_adj[c]), default=0)

        max_rank = max(rank_up.values()) if rank_up else 0

        print(f"\n{'=' * 70}", flush=True)
        print(f"n={n}: {len(jdz)} jdz edges, Δfc≥0 rank={max_rank} ({time.time() - t0:.1f}s)", flush=True)
        print(f"{'=' * 70}", flush=True)

        # === 1. Enumerate ALL paths of length 2+ in Δfc≥0 subgraph ===
        # For each node with rank ≥ 2, find a length-2 path
        # For rank ≥ 3, find a length-3 path
        if max_rank >= 2:
            print(f"\n  Sample rank-{max_rank} paths:", flush=True)
            shown = 0
            for start in topo:
                if rank_up.get(start, 0) < max_rank:
                    continue
                if shown >= 3:
                    break
                # Find longest path from start
                path = [start]
                cur = start
                while rank_up.get(cur, 0) > 0:
                    best_next = None
                    best_rank = -1
                    for nxt in up_adj.get(cur, []):
                        if rank_up.get(nxt, 0) > best_rank:
                            best_rank = rank_up.get(nxt, 0)
                            best_next = nxt
                    if best_next is None:
                        break
                    path.append(best_next)
                    cur = best_next

                # Show path with fc values and diffs
                fcs = [fc(c, n) for c in path]
                diffs = []
                for i in range(len(path) - 1):
                    u, v = path[i], path[i + 1]
                    changed = [j for j in range(n) if u[j] != v[j]]
                    diffs.append((fc(v, n) - fc(u, n), changed))

                print(f"    Path (len {len(path)-1}):", flush=True)
                for i, c in enumerate(path):
                    rank_str = f"r={rank_up.get(c, '?')}"
                    print(f"      [{i}] {c}  fc={fc(c,n)} {rank_str}", flush=True)
                for i, (dfc, changed) in enumerate(diffs):
                    print(f"        → Δfc={dfc:+d}, changed positions: {changed}", flush=True)
                shown += 1

        # === 2. Δfc distribution in Δfc≥0 edges by source rank ===
        print(f"\n  Δfc by source rank in Δfc≥0 subgraph:", flush=True)
        for r in range(max_rank + 1):
            edges_at_r = []
            for u in up_nodes:
                if rank_up.get(u, 0) == r:
                    for v in up_adj[u]:
                        edges_at_r.append((u, v))
            if edges_at_r:
                dfc_dist = Counter(fc(v, n) - fc(u, n) for u, v in edges_at_r)
                print(f"    rank={r}: {len(edges_at_r)} edges, Δfc={dict(sorted(dfc_dist.items()))}", flush=True)

        # === 3. Max total fc gain along any Δfc≥0 path ===
        max_gain = {}
        for c in reversed(topo):
            if not up_adj[c]:
                max_gain[c] = 0
            else:
                max_gain[c] = max(
                    (fc(v, n) - fc(c, n)) + max_gain[v]
                    for v in up_adj[c]
                )
        total_max_gain = max(max_gain.values()) if max_gain else 0
        gain_dist = Counter(max_gain.values())
        print(f"\n  Max total fc gain along Δfc≥0 path: {total_max_gain}", flush=True)
        print(f"  Gain distribution: {dict(sorted(gain_dist.items()))}", flush=True)

        # === 4. Can Δfc≥0 rank be 4? Check rank-3 sinks: do they have ANY outgoing Δfc≥0 edges to nodes outside the subgraph? ===
        rank3_sinks = [c for c in up_nodes if rank_up.get(c, 0) == 0
                       and any(rank_up.get(u, -1) == 1 for u in up_nodes
                               if c in up_adj.get(u, []))]
        # Actually, check nodes at end of rank-3 paths: what are their successors?
        if max_rank >= 3:
            # Find all rank-3 nodes (starts of longest paths)
            rank3_starts = [c for c in up_nodes if rank_up[c] == 3]
            print(f"\n  Rank-3 starts: {len(rank3_starts)}", flush=True)

            # For each rank-3 start, look at where the path ends
            # The end node has rank 0 in Δfc≥0 → no outgoing Δfc≥0 edges
            # Does it have outgoing Δfc<0 edges in jdz?
            ends_with_down = 0
            ends_dead = 0
            for start in rank3_starts[:100]:
                # Follow to end of rank path
                cur = start
                while rank_up.get(cur, 0) > 0:
                    for nxt in up_adj.get(cur, []):
                        if rank_up.get(nxt, 0) == rank_up[cur] - 1:
                            cur = nxt
                            break
                # cur is now rank-0 endpoint
                has_down = any(fc(v, n) < fc(cur, n) for v in jdz_adj.get(cur, []))
                if has_down:
                    ends_with_down += 1
                else:
                    ends_dead += 1

            checked = min(100, len(rank3_starts))
            print(f"  Rank-3 path endpoints: {ends_with_down}/{checked} have Δfc<0 out-edge, {ends_dead}/{checked} are dead ends", flush=True)

        # === 5. For each edge, compute ΔΦ for Φ = -fc + 4·rank_up ===
        # (trying various coefficients)
        print(f"\n  Potential function tests on ALL jdz edges:", flush=True)
        for alpha in [1, 2, 3, 4, 5, 6, 7, 8]:
            # Φ(c) = alpha * rank_up(c) - fc(c)
            # For Δfc<0: ΔΦ = alpha*(R(v)-R(u)) - Δfc
            #   R(v)-R(u) ∈ [-3,3], Δfc ∈ [-n+3, -1]
            #   ΔΦ = alpha*(R(v)-R(u)) + |Δfc| → could be very positive
            # For Δfc≥0: ΔΦ = alpha*(R(v)-R(u)) - Δfc
            #   R(v)-R(u) ≤ -1, Δfc ≥ 0
            #   ΔΦ ≤ -alpha + 2 → need alpha > 2
            viol = 0
            for u, v in jdz:
                ru = rank_up.get(u, 0)
                rv = rank_up.get(v, 0)
                phi_u = alpha * ru - fc(u, n)
                phi_v = alpha * rv - fc(v, n)
                if phi_v >= phi_u:
                    viol += 1
            pct = 100 * viol / len(jdz)
            print(f"    Φ = {alpha}·rank_up - fc: {viol}/{len(jdz)} violations ({pct:.1f}%)", flush=True)

        # And Φ = fc + alpha * rank_up (try negative alpha for fc contribution)
        for alpha in [-1, -2, -3, -4]:
            viol = 0
            for u, v in jdz:
                ru = rank_up.get(u, 0)
                rv = rank_up.get(v, 0)
                phi_u = fc(u, n) + alpha * ru
                phi_v = fc(v, n) + alpha * rv
                if phi_v >= phi_u:
                    viol += 1
            pct = 100 * viol / len(jdz)
            print(f"    Φ = fc + ({alpha})·rank_up: {viol}/{len(jdz)} violations ({pct:.1f}%)", flush=True)

        elapsed = time.time() - t0
        print(f"\n  Time: {elapsed:.1f}s", flush=True)

if __name__ == '__main__':
    main()
