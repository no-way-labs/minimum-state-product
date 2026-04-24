#!/usr/bin/env python3
"""
CONVERGENCE PROOF 71: Verify rank ≤ 3 at n=12, analyze step types
==================================================================
1. Confirm Δfc≥0 rank ≤ 3 at n=12
2. For every Δfc≥0 edge: what anomalous entry drives it?
3. Classify rank-3 paths by anomalous entry sequence
4. WHY can't paths have length 4? What blocks the 4th step?
5. Can we prove rank ≤ 3 from the table structure?
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

def classify_anom(pos, L, S, R, out, n):
    if pos == 0:
        return f"bot({L},{S},{R})→{out}"
    elif pos == 1:
        return f"low({L},{S},{R})→{out}"
    elif pos == n - 2:
        return f"high({L},{S},{R})→{out}"
    elif pos == n - 1:
        return f"top({L},{S},{R})→{out}"
    else:
        return f"mid({L},{S},{R})→{out}"

def build_full_data(n_val):
    ms, fs = build_system(n_val)
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    # All transitions from bad configs
    anom_edges = []
    dfc_le0_adj = defaultdict(list)
    step_info = {}  # (c, succ) -> (pos, L, S, R, out)
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
                    step_info[(c, succ)] = (i, L, S, R, out)
                    if dfc <= 0:
                        dfc_le0_adj[c].append(succ)
                    if out != L and out != R:
                        anom_edges.append((c, succ, i, dfc))

    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_target_map = defaultdict(list)
    anom_step_info = {}
    for c, succ, i, dfc in anom_edges:
        anom_target_map[succ].append(c)
        anom_step_info[(c, succ)] = (i, c[(i-1)%n_val], c[i], c[(i+1)%n_val], succ[i])

    # Build excursion edges with anomalous step info
    exc_edges = []
    for b in set(s for _, s, _, _ in anom_edges):
        visited = {b}
        queue = [b]
        head = 0
        while head < len(queue):
            node = queue[head]
            head += 1
            if node in anom_sources:
                for src in anom_target_map.get(b, []):
                    exc_edges.append((src, node, b, anom_step_info.get((src, b))))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append(nxt)

    return exc_edges, ms, fs

def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def int_j_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in [7, 9, 11, 12]:
        t0 = time.time()
        exc_edges_full, ms, fs = build_full_data(n_val)
        n = n_val

        # jdz edges with anomalous step info
        jdz = []
        for u, v, b, info in exc_edges_full:
            if int_21(v, n) - int_21(u, n) != 0:
                continue
            if int_j_20(v, n) - int_j_20(u, n) != 0:
                continue
            jdz.append((u, v, info))

        jdz_unique = {}
        for u, v, info in jdz:
            if (u, v) not in jdz_unique:
                jdz_unique[(u, v)] = info

        jdz_edges = list(jdz_unique.keys())

        if not jdz_edges:
            print(f"n={n}: no jdz edges")
            continue

        print(f"\n{'=' * 70}", flush=True)
        print(f"n={n}: {len(jdz_edges)} jdz edges ({time.time() - t0:.1f}s)", flush=True)
        print(f"{'=' * 70}", flush=True)

        # Build Δfc≥0 subgraph
        up_adj = defaultdict(list)
        up_nodes = set()
        up_edge_info = {}
        for u, v in jdz_edges:
            if fc(v, n) >= fc(u, n):
                up_adj[u].append(v)
                up_nodes.add(u)
                up_nodes.add(v)
                up_edge_info[(u, v)] = jdz_unique[(u, v)]

        # Topological sort + rank
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

        is_dag = len(topo) == len(up_nodes)
        print(f"  Δfc≥0 DAG: {is_dag} ({len(topo)}/{len(up_nodes)})", flush=True)

        if not is_dag:
            print("  WARNING: NOT A DAG!")
            continue

        rank_up = {}
        for c in reversed(topo):
            rank_up[c] = max((rank_up[s] + 1 for s in up_adj[c]), default=0)
        max_rank = max(rank_up.values()) if rank_up else 0
        rank_dist = Counter(rank_up.values())
        print(f"  Max rank: {max_rank}", flush=True)
        print(f"  Rank distribution: {dict(sorted(rank_dist.items()))}", flush=True)

        # === Anomalous entry classification for Δfc≥0 edges ===
        print(f"\n  Anomalous entry types in Δfc≥0 edges:", flush=True)
        entry_types = Counter()
        for (u, v), info in up_edge_info.items():
            if info:
                pos, L, S, R, out = info
                etype = classify_anom(pos, L, S, R, out, n)
                entry_types[etype] += 1
            else:
                entry_types["(unknown)"] += 1
        for etype, cnt in entry_types.most_common():
            print(f"    {etype}: {cnt}", flush=True)

        # === Rank-3 path analysis ===
        if max_rank >= 3:
            print(f"\n  Rank-3 path analysis:", flush=True)
            rank3_nodes = [c for c in up_nodes if rank_up[c] == 3]
            print(f"    {len(rank3_nodes)} rank-3 nodes", flush=True)

            # Trace all rank-3 paths (enumerate all length-3 paths from rank-3 nodes)
            path_type_seqs = Counter()
            path_dfc_seqs = Counter()
            path_boundary_seqs = Counter()
            n_paths = 0

            for start in rank3_nodes:
                # Enumerate all length-3 paths
                stack = [(start, [start], [])]
                while stack:
                    cur, path, infos = stack.pop()
                    if len(path) == 4:
                        # Got a length-3 path
                        n_paths += 1
                        # Classify
                        types = []
                        dfcs = []
                        bdry_changes = []
                        for i in range(3):
                            u, v = path[i], path[i + 1]
                            dfc = fc(v, n) - fc(u, n)
                            dfcs.append(dfc)
                            info = up_edge_info.get((u, v))
                            if info:
                                pos, L, S, R, out = info
                                etype = classify_anom(pos, L, S, R, out, n)
                                types.append(etype)
                            else:
                                types.append("?")
                            # Boundary change
                            bdry_u = (u[0], u[1], u[n-2], u[n-1])
                            bdry_v = (v[0], v[1], v[n-2], v[n-1])
                            bdry_changes.append(f"{bdry_u}→{bdry_v}")

                        path_type_seqs[tuple(types)] += 1
                        path_dfc_seqs[tuple(dfcs)] += 1
                        continue

                    if rank_up.get(cur, 0) == 0:
                        continue

                    for nxt in up_adj.get(cur, []):
                        if rank_up.get(nxt, 0) == rank_up[cur] - 1:
                            stack.append((nxt, path + [nxt], infos + [up_edge_info.get((cur, nxt))]))

            print(f"    {n_paths} rank-3 paths", flush=True)

            print(f"\n    Entry type sequences:", flush=True)
            for seq, cnt in path_type_seqs.most_common(20):
                print(f"      {' → '.join(seq)}: {cnt}", flush=True)

            print(f"\n    Δfc sequences:", flush=True)
            for seq, cnt in path_dfc_seqs.most_common(10):
                print(f"      {seq}: {cnt}", flush=True)

        # === Why no rank 4? Check: for rank-0 sinks, what configs are they? ===
        if max_rank >= 3:
            # Find rank-0 sinks that are at the END of rank-3 paths
            rank0_at_end = set()
            for start in rank3_nodes[:50]:
                cur = start
                for _ in range(3):
                    for nxt in up_adj.get(cur, []):
                        if rank_up.get(nxt, 0) == rank_up[cur] - 1:
                            cur = nxt
                            break
                rank0_at_end.add(cur)

            print(f"\n  Rank-0 endpoint analysis ({len(rank0_at_end)} endpoints):", flush=True)

            # What are their (P0, P1, Pn-2, Pn-1) boundaries?
            bdry_count = Counter()
            for c in rank0_at_end:
                bdry = (c[0], c[1], c[n-2], c[n-1])
                bdry_count[bdry] += 1
            print(f"    Boundary values: {dict(bdry_count.most_common(10))}", flush=True)

            # Do they have ANY outgoing jdz edges?
            jdz_adj = defaultdict(list)
            for u, v in jdz_edges:
                jdz_adj[u].append(v)

            n_has_out = sum(1 for c in rank0_at_end if jdz_adj.get(c))
            n_has_down = sum(1 for c in rank0_at_end
                            if any(fc(v, n) < fc(c, n) for v in jdz_adj.get(c, [])))
            print(f"    Has ANY jdz out-edge: {n_has_out}/{len(rank0_at_end)}", flush=True)
            print(f"    Has Δfc<0 out-edge: {n_has_down}/{len(rank0_at_end)}", flush=True)

            # For rank-3 starts: what's their boundary?
            bdry_start = Counter()
            for c in rank3_nodes:
                bdry = (c[0], c[1], c[n-2], c[n-1])
                bdry_start[bdry] += 1
            print(f"    Rank-3 start boundaries: {dict(bdry_start.most_common(10))}", flush=True)

        elapsed = time.time() - t0
        print(f"\n  Time: {elapsed:.1f}s", flush=True)

if __name__ == '__main__':
    main()
