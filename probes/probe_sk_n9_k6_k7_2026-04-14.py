#!/usr/bin/env python3
"""n=9 binary-count invariance + k=6, k=7 structural extension.

Objectives:

  (1) Binary-count invariance at n=9: predict |SK| = 2^9 - 18 - 2 = 492
      across k ∈ {3, 4, 5, 6, 7}. (n=9 is odd, ε=2.)
  (2) Edges/proc at n=9: predict 2^7 - 2 = 126.
  (3) k=6 saturated data point: (n=8, k=6). Compare against (n=7, k=6)
      (which had |E|=124 and is nominally "boundary"). This determines
      whether the fiber-saturation boundary holds at k=6 or whether the
      closed form f(6) = 124 is already achieved at n-k=1.
  (4) k=7 saturated data point: (n=9, k=7), expected f(7) = 9·2^5 − 28 + 4 = 264.
  (5) Girth verification at k=6 and k=7: predict 2k = 12 and 14.
  (6) Per-band edge breakdown at each point.

Seeded enumerator — mover seq = [0..n-1]*2 — avoids free DFS.
"""

from itertools import product as iproduct
from collections import defaultdict, Counter, deque
import time
import sys


def enumerate_sweep_cycles(ms, n, max_found=5, time_budget=180.0):
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
    bpos = [i for i, m in enumerate(ms) if m == 2]
    verts = set()
    for c in kernel:
        verts.add(tuple(c[i] for i in bpos))
    edges = defaultdict(int)
    kset = set(kernel)
    per_mover = Counter()
    for u in kernel:
        for v, p in adj.get(u, ()):
            if v not in kset: continue
            per_mover[p] += 1
            if p in bpos:
                bu = tuple(u[i] for i in bpos)
                bv = tuple(v[i] for i in bpos)
                if bu != bv:
                    edges[(bu, bv)] += 1
    return verts, dict(edges), dict(per_mover)


def band_breakdown(edges, k):
    bands = Counter()
    for (u, v) in edges:
        wu, wv = sum(u), sum(v)
        if wu < wv:
            bands[(wu, wv)] += 1
        else:
            bands[(wv, wu)] += 1
    return bands


def girth_on_vertices(verts, edge_keys):
    """Shortest directed cycle among given verts using BFS from each."""
    if not verts:
        return None
    proj_adj = defaultdict(list)
    for (u, v) in edge_keys:
        if u in verts and v in verts:
            proj_adj[u].append(v)
    best = None
    for src in verts:
        dist = {src: 0}
        q = deque([src])
        found = None
        while q:
            u = q.popleft()
            for v in proj_adj.get(u, ()):
                if v == src:
                    cand = dist[u] + 1
                    if found is None or cand < found:
                        found = cand
                    continue
                if v not in dist:
                    dist[v] = dist[u] + 1
                    q.append(v)
        if found is not None:
            if best is None or found < best:
                best = found
    return best


def middle_weights(k):
    if k % 2 == 1:
        m = k // 2
        return {m, m + 1}
    else:
        m = k // 2
        return {m - 1, m, m + 1}


def run_point(ms, n, k, time_budget=180.0):
    P = 1
    for m in ms: P *= m
    print(f"\n{'='*70}")
    print(f"n={n} k={k}  ms={ms}  product={P}  threshold={4*3**(n-2)}")
    print(f"{'='*70}")
    t0 = time.time()
    cycles = enumerate_sweep_cycles(ms, n, max_found=3, time_budget=time_budget)
    elapsed = time.time() - t0
    print(f"  enumerate: {len(cycles)} cycles in {elapsed:.1f}s")
    if not cycles:
        return None

    cycle, movers, det = cycles[0]
    good_set = set(cycle)
    ng, _, adj = build_forced_graph(ms, n, det, good_set)
    sk, rounds = sink_kernel(ng, adj)
    verts, edges, per_mover = project_kernel(sk, adj, ms)

    per_mover_vals = set(per_mover.values())
    epp = next(iter(per_mover_vals)) if len(per_mover_vals) == 1 else str(per_mover_vals)

    print(f"  |SK|={len(sk)}  rounds={rounds}")
    print(f"  edges/proc={epp}  |verts_proj|={len(verts)}/{2**k}  "
          f"|E_proj|={len(edges)}")

    bands = band_breakdown(edges, k)
    print(f"  band breakdown:")
    for (wu, wv) in sorted(bands):
        print(f"    w{wu}↔w{wv}: {bands[(wu, wv)]}")

    # Middle-layer girth.
    mw = middle_weights(k)
    mid_verts = {v for v in verts if sum(v) in mw}
    mid_edges = [(u, v) for (u, v) in edges
                 if u in mid_verts and v in mid_verts]
    girth = girth_on_vertices(mid_verts, mid_edges)
    print(f"  middle layer (weights {sorted(mw)}): |V|={len(mid_verts)}  "
          f"|E|={len(mid_edges)}  girth={girth}")
    return {
        "ms": ms, "n": n, "k": k, "P": P,
        "sk": len(sk), "epp": epp,
        "verts_count": len(verts),
        "edges_count": len(edges),
        "bands": dict(bands),
        "girth": girth,
    }


def main():
    # n=9 binary-count invariance sweep.
    n9_points = [
        ((2,2,2,3,3,3,3,3,3), 9, 3),
        ((2,2,2,2,3,3,3,3,3), 9, 4),
        ((2,2,2,2,2,3,3,3,3), 9, 5),
        ((2,2,2,2,2,2,3,3,3), 9, 6),
        ((2,2,2,2,2,2,2,3,3), 9, 7),
    ]
    # k=6 saturation check.
    k6_points = [
        ((2,2,2,2,2,2,3,3), 8, 6),   # n-k=2, should be saturated
    ]

    results = []
    for (ms, n, k) in n9_points + k6_points:
        r = run_point(ms, n, k, time_budget=240.0)
        if r is not None:
            results.append(r)

    print("\n\n" + "=" * 70)
    print("SUMMARY TABLE")
    print("=" * 70)
    print(f"{'n':<3}{'k':<3}{'P':<6}{'|SK|':<8}{'e/proc':<8}{'|E_proj|':<10}"
          f"{'girth':<7}{'|V_proj|':<10}")
    for r in results:
        print(f"{r['n']:<3}{r['k']:<3}{r['P']:<6}{r['sk']:<8}"
              f"{str(r['epp']):<8}{r['edges_count']:<10}"
              f"{str(r['girth']):<7}{r['verts_count']:<10}")

    print("\nPREDICTIONS:")
    print("  n=9: |SK| = 2^9 - 18 - 2 = 492 (odd)")
    print("  n=9: edges/proc = 2^7 - 2 = 126")
    print("  n=8: |SK| = 2^8 - 16 = 240 (even)")
    print("  f(3)=10, f(4)=24, f(5)=56, f(6)=124, f(7)=264  "
          "(9*2^(k-2) - 4k + 4)")
    print("  girth(k) = 2k:  girth(6)=12, girth(7)=14")

    # Binary-count invariance check at n=9.
    n9_sks = [r["sk"] for r in results if r["n"] == 9]
    n9_epps = [r["epp"] for r in results if r["n"] == 9]
    print(f"\nn=9 binary-count invariance:")
    print(f"  |SK| values: {set(n9_sks)}  (predicted {{492}})")
    print(f"  e/proc values: {set(n9_epps)}  (predicted {{126}})")


if __name__ == "__main__":
    main()
