#!/usr/bin/env python3
"""Braided SCC structure of SK middle-layer subgraphs at k=4, k=5.

At k≥4 the middle layer of the SK projection is not Hamiltonian (per
probe_sk_nk_sweep_2026-04-14.py). Question: what structure does it
actually have? Is it one big SCC composed of multiple overlapping
smaller cycles (braided), or several disjoint SCCs?

Additional questions:
  (A) Is the FULL projection (all 2^k vertices) Hamiltonian even if
      the middle-layer subgraph isn't?
  (B) Which specific edges are missing at k=5 (24 of 30 used)?
  (C) Which edges are missing at the n-k=1 fiber-boundary (20 vs 24
      at (5,4); 52 vs 56 at (6,5))?

Test points:
  (6, 4) — k=4 saturated, thick middle (weight-{1,2,3}, 14 verts)
  (7, 5) — k=5 saturated, middle (weight-{2,3}, 20 verts)
  (5, 4) — k=4 non-saturated, compare what's missing vs (6, 4)
  (6, 5) — k=5 non-saturated, compare what's missing vs (7, 5)
"""

from itertools import product as iproduct
from collections import defaultdict, Counter, deque
import time
import sys


def enumerate_sweep_cycles(ms, n, max_found=15, time_budget=60.0):
    mover_seq = list(range(n)) * 2
    L = len(mover_seq)
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen = set()
    t0 = time.time()

    def dfs(step, config, det, path):
        if len(found) >= max_found or time.time() - t0 > time_budget:
            return
        if step == L:
            if config == path[0]:
                cycle_tup = tuple(path)
                if cycle_tup not in seen:
                    seen.add(cycle_tup)
                    found.append((list(path), list(mover_seq), dict(det)))
            return
        p = mover_seq[step]
        Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
        key_m = (p, Lp, Sp, Rp)
        forced_out = det.get(key_m)
        for new_val in range(ms[p]):
            if new_val == Sp: continue
            if forced_out is not None and forced_out != new_val: continue
            new_det = dict(det)
            new_det[key_m] = new_val
            consistent = True
            for i in range(n):
                if i == p: continue
                Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]
                ki = (i, Li, Si, Ri)
                if ki in new_det and new_det[ki] != Si:
                    consistent = False; break
                new_det[ki] = Si
            if not consistent: continue
            nc = list(config); nc[p] = new_val; nc = tuple(nc)
            if step + 1 < L and nc in set(path):
                continue
            dfs(step+1, nc, new_det, path + [nc])

    for start in all_starts:
        if len(found) >= max_found or time.time() - t0 > time_budget:
            break
        dfs(0, start, {}, [start])
    return found


def build_forced_graph(ms, n, det, good_set):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    ng_set = set(non_good)
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p-1)%n]; Sp = c[p]; Rp = c[(p+1)%n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c); nc[p] = det[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append((nc, p))
    return non_good, ng_set, adj


def sink_kernel(non_good, adj):
    remaining = set(non_good)
    rounds = 0
    while True:
        sinks = set()
        for c in remaining:
            has_out = False
            for tgt, _ in adj.get(c, []):
                if tgt in remaining:
                    has_out = True; break
            if not has_out:
                sinks.add(c)
        if not sinks:
            break
        remaining -= sinks
        rounds += 1
    return remaining, rounds


def project_kernel(kernel, adj, ms):
    """Compute the binary-cube projection: (verts, edges)."""
    bpos = [i for i, m in enumerate(ms) if m == 2]
    verts = set()
    for c in kernel:
        verts.add(tuple(c[i] for i in bpos))
    edges = set()  # directed
    kset = set(kernel)
    for u in kernel:
        for v, p in adj.get(u, ()):
            if v not in kset: continue
            if p in bpos:
                bu = tuple(u[i] for i in bpos)
                bv = tuple(v[i] for i in bpos)
                if bu != bv:
                    edges.add((bu, bv))
    return verts, edges


def hamming(a, b):
    return sum(x != y for x, y in zip(a, b))


def tarjan_scc(verts, adj):
    """Return list of SCCs sorted by size descending."""
    index_map = {}
    lowlink = {}
    on_stack = set()
    stack = []
    counter = [0]
    sccs = []
    def sc(v):
        index_map[v] = counter[0]
        lowlink[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        for w in adj.get(v, ()):
            if w not in verts:
                continue
            if w not in index_map:
                sc(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index_map[w])
        if lowlink[v] == index_map[v]:
            comp = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                comp.append(w)
                if w == v:
                    break
            sccs.append(comp)
    sys.setrecursionlimit(max(sys.getrecursionlimit(), len(verts) * 4 + 100))
    for v in verts:
        if v not in index_map:
            sc(v)
    sccs.sort(key=len, reverse=True)
    return sccs


def shortest_cycle_length(scc_verts, adj):
    vset = set(scc_verts)
    best = None
    for src in vset:
        # BFS from src, looking for shortest path back to src.
        dist = {src: 0}
        q = deque([src])
        found = None
        while q:
            u = q.popleft()
            for v in adj.get(u, ()):
                if v not in vset: continue
                if v == src:
                    cand = dist[u] + 1
                    if found is None or cand < found:
                        found = cand
                    continue
                if v not in dist:
                    dist[v] = dist[u] + 1
                    q.append(v)
        if found is not None and (best is None or found < best):
            best = found
    return best


def cycle_length_histogram(scc_verts, adj, max_len=12):
    """Count simple cycles up to max_len in the SCC. Uses DFS with
    length bound; reports counts by length."""
    vset = set(scc_verts)
    counts = Counter()
    # Canonicalize each cycle by rotating to start at its min vertex.
    found_cycles = set()
    def dfs(start, cur, path, depth):
        if depth > max_len:
            return
        for v in adj.get(cur, ()):
            if v not in vset: continue
            if v == start:
                if depth + 1 >= 2:
                    cyc = tuple(path)
                    # Rotate to start at min
                    mi = cyc.index(min(cyc))
                    norm = cyc[mi:] + cyc[:mi]
                    if norm not in found_cycles:
                        found_cycles.add(norm)
                        counts[depth + 1] += 1
                continue
            if v in path:
                continue
            dfs(start, v, path + (v,), depth + 1)
    # Only try starts from min-vertex of cycles for efficiency.
    for v in sorted(vset):
        dfs(v, v, (v,), 1)
    return counts


def hamilton_search_full(verts, adj):
    """Full DFS Hamilton cycle search on verts."""
    verts = list(verts)
    nverts = len(verts)
    if nverts > 25:
        return "too_large"
    # Try every start (redundant but safe).
    vset = set(verts)
    for start_idx in range(min(3, nverts)):
        start = verts[start_idx]
        path = [start]
        visited = {start}
        def dfs():
            if len(path) == nverts:
                return start in adj.get(path[-1], [])
            cur = path[-1]
            for nxt in adj.get(cur, ()):
                if nxt in vset and nxt not in visited:
                    path.append(nxt)
                    visited.add(nxt)
                    if dfs():
                        return True
                    path.pop()
                    visited.discard(nxt)
            return False
        sys.setrecursionlimit(max(sys.getrecursionlimit(), nverts * 4 + 100))
        if dfs():
            return nverts
    return None


def run(ms, label):
    n = len(ms)
    bpos = [i for i, m in enumerate(ms) if m == 2]
    k = len(bpos)
    print(f"\n{'='*66}")
    print(f"{label}  ms={ms}  n={n}  k={k}")
    print(f"{'='*66}")

    t0 = time.time()
    cycles = enumerate_sweep_cycles(ms, n, max_found=5)
    if not cycles:
        print("  no cycles found")
        return None
    cycle, movers, det = cycles[0]
    good_set = set(cycle)
    ng, _, adj = build_forced_graph(ms, n, det, good_set)
    sk, rounds = sink_kernel(ng, adj)
    verts, edges = project_kernel(sk, adj, ms)
    print(f"  |SK|={len(sk)}  |verts_proj|={len(verts)}  |edges_proj|={len(edges)}")

    # Directed adjacency dict on binary projection.
    proj_adj = defaultdict(list)
    for (u, v) in edges:
        proj_adj[u].append(v)

    # Middle-layer verts.
    if k % 2 == 1:
        m_mid = k // 2
        mid_weights = {m_mid, m_mid + 1}
    else:
        m_mid = k // 2
        mid_weights = {m_mid - 1, m_mid, m_mid + 1}
    mid_verts = {v for v in verts if sum(v) in mid_weights}
    mid_edges = {(u, v) for (u, v) in edges
                 if u in mid_verts and v in mid_verts}
    print(f"\n  middle layer (weights {sorted(mid_weights)}):")
    print(f"    |mid_verts|={len(mid_verts)}  |mid_edges|={len(mid_edges)}")

    # SCCs of middle-layer subgraph.
    mid_proj_adj = defaultdict(list)
    for (u, v) in mid_edges:
        mid_proj_adj[u].append(v)
    sccs_mid = tarjan_scc(mid_verts, mid_proj_adj)
    print(f"    SCCs: {len(sccs_mid)}  sizes: {[len(s) for s in sccs_mid]}")

    if sccs_mid:
        largest = sccs_mid[0]
        if len(largest) >= 2:
            girth = shortest_cycle_length(largest, mid_proj_adj)
            print(f"    girth of largest SCC: {girth}")
            hist = cycle_length_histogram(largest, mid_proj_adj, max_len=10)
            if hist:
                print(f"    cycle length histogram (up to 10): {dict(hist)}")

    # Hamilton search on FULL projection.
    if len(verts) <= 20:
        ham_full = hamilton_search_full(verts, proj_adj)
        print(f"\n  FULL projection Hamilton search ({len(verts)} verts): "
              f"{ham_full}")
    else:
        print(f"\n  FULL projection has {len(verts)} verts "
              f"— skipping Hamilton search")

    # Check which middle-layer edges (of max possible) are missing.
    max_mid_edges = set()
    for u in mid_verts:
        for v in mid_verts:
            if u == v: continue
            if hamming(u, v) == 1:
                max_mid_edges.add((u, v))
    missing = max_mid_edges - mid_edges
    print(f"\n  middle-layer max possible directed edges: {len(max_mid_edges)}")
    print(f"  missing from SK: {len(missing)}")
    if len(missing) <= 12:
        for (u, v) in sorted(missing):
            print(f"    {u} -> {v}  [w{sum(u)}->w{sum(v)}]")

    return {
        "ms": ms, "k": k, "sk_size": len(sk),
        "proj_verts": verts, "proj_edges": edges,
        "mid_verts": mid_verts, "mid_edges": mid_edges,
        "sccs_mid": sccs_mid,
    }


def compare_missing(saturated_result, sub_result, label):
    """Compare edge sets: which edges are missing at n-k=1 vs saturated?"""
    print(f"\n{'='*66}")
    print(f"FIBER-BOUNDARY DIFF  {label}")
    print(f"{'='*66}")
    if saturated_result is None or sub_result is None:
        return
    sat_edges = saturated_result["proj_edges"]
    sub_edges = sub_result["proj_edges"]
    only_sat = sat_edges - sub_edges
    only_sub = sub_edges - sat_edges
    print(f"  saturated |E|={len(sat_edges)}  sub |E|={len(sub_edges)}")
    print(f"  in saturated only (missing at n-k=1): {len(only_sat)}")
    for (u, v) in sorted(only_sat):
        print(f"    {u} -> {v}  [w{sum(u)}->w{sum(v)}]")
    print(f"  in sub only: {len(only_sub)}")
    for (u, v) in sorted(only_sub):
        print(f"    {u} -> {v}  [w{sum(u)}->w{sum(v)}]")


def main():
    r64 = run((2,2,2,2,3,3), "k=4 saturated (n=6)")
    r75 = run((2,2,2,2,2,3,3), "k=5 saturated (n=7)")
    r54 = run((2,2,2,2,3), "k=4 boundary n-k=1 (n=5)")
    r65 = run((2,2,2,2,2,3), "k=5 boundary n-k=1 (n=6)")

    compare_missing(r64, r54, "k=4 sat (n=6) vs boundary (n=5)")
    compare_missing(r75, r65, "k=5 sat (n=7) vs boundary (n=6)")


if __name__ == "__main__":
    main()
