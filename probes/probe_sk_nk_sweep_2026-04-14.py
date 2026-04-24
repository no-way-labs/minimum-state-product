#!/usr/bin/env python3
"""(n, k) parameter sweep for SK invariant.

Objectives:
  (1) Lock binary-count invariance: vary k at fixed n, verify |SK|
      and edges/proc are constant.
  (2) Find a closed-form for distinct binary-projection edge count
      as a function of (n, k).
  (3) At k ≥ 4, test whether the middle-layer subgraph of the SK
      contains a Hamiltonian cycle (using a DFS Hamilton search).

Configurations tested (all consecutive binary, filled with ternary):
  n=5: k=3, 4            (filling with ternary)
  n=6: k=3, 4, 5
  n=7: k=3, 4, 5, 6
  n=8: k=3, 4, 5, 6
"""

from itertools import product as iproduct
from collections import defaultdict, Counter
import time


def make_ms(n, k):
    """ms with k consecutive binary, filled with ternary."""
    return tuple([2]*k + [3]*(n-k))


def enumerate_sweep_cycles(ms, n, max_found=30, time_budget=120.0):
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


def hamming(a, b):
    return sum(x != y for x, y in zip(a, b))


def analyze_projection(kernel, adj, ms, n):
    bpos = [i for i, m in enumerate(ms) if m == 2]
    k = len(bpos)
    verts = set()
    by_weight = defaultdict(int)
    for c in kernel:
        bp = tuple(c[i] for i in bpos)
        verts.add(bp)
        by_weight[sum(bp)] += 1
    edges = defaultdict(int)
    edges_per_mover = Counter()
    kset = set(kernel)
    for u in kernel:
        for v, p in adj.get(u, ()):
            if v not in kset: continue
            edges_per_mover[p] += 1
            if p in bpos:
                bu = tuple(u[i] for i in bpos)
                bv = tuple(v[i] for i in bpos)
                if bu != bv:
                    edges[(bu, bv)] += 1
    return {
        "sk_size": len(kernel),
        "k": k,
        "verts": verts,
        "by_weight": dict(by_weight),
        "edges": dict(edges),
        "edges_per_mover": dict(edges_per_mover),
        "distinct_proj_edges": len(edges),
    }


def middle_layer_hamilton_search(info):
    """Find a Hamiltonian cycle in the middle-layer subgraph of the
    binary projection. Returns the cycle length if found, else None."""
    k = info["k"]
    edges = info["edges"]

    # Pick middle weight classes.
    if k % 2 == 1:
        m = k // 2
        mid_weights = {m, m+1}
    else:
        m = k // 2
        mid_weights = {m-1, m, m+1}  # thick middle

    # Middle-layer vertex set and directed adjacency.
    verts = [v for v in info["verts"] if sum(v) in mid_weights]
    nverts = len(verts)
    if nverts == 0:
        return None
    vset = set(verts)
    adj_mid = defaultdict(list)
    for (u, v), mult in edges.items():
        if u in vset and v in vset:
            adj_mid[u].append(v)

    # Hamiltonian cycle DFS with early termination.
    # For k <= 5 this is tractable (≤ 20 vertices).
    if nverts > 25:
        return "too_large"
    start = verts[0]
    path = [start]
    visited = {start}

    def dfs():
        if len(path) == nverts:
            if start in adj_mid.get(path[-1], []):
                return True
            return False
        cur = path[-1]
        for nxt in adj_mid.get(cur, []):
            if nxt not in visited:
                path.append(nxt)
                visited.add(nxt)
                if dfs():
                    return True
                path.pop()
                visited.discard(nxt)
        return False

    import sys
    sys.setrecursionlimit(10000)
    if dfs():
        return nverts
    return None


def run_point(n, k):
    ms = make_ms(n, k)
    P = 1
    for m in ms: P *= m
    t0 = time.time()
    cycles = enumerate_sweep_cycles(ms, n, max_found=15, time_budget=60.0)
    elapsed = time.time() - t0
    if not cycles:
        return {
            "n": n, "k": k, "ms": ms, "P": P,
            "cycles": 0, "elapsed": elapsed,
            "sk": None, "edges_per_proc": None, "distinct_edges": None,
            "ham": None,
        }

    # Analyze first cycle (all are rigid anyway).
    cycle, movers, det = cycles[0]
    good_set = set(cycle)
    ng, _, adj = build_forced_graph(ms, n, det, good_set)
    sk, rounds = sink_kernel(ng, adj)
    info = analyze_projection(sk, adj, ms, n)

    per_mover = set(info["edges_per_mover"].values())
    epp = next(iter(per_mover)) if len(per_mover) == 1 else str(per_mover)

    ham_len = None
    if k >= 3:
        ham_len = middle_layer_hamilton_search(info)

    return {
        "n": n, "k": k, "ms": ms, "P": P,
        "cycles": len(cycles), "elapsed": elapsed,
        "sk": info["sk_size"],
        "edges_per_proc": epp,
        "distinct_edges": info["distinct_proj_edges"],
        "ham": ham_len,
    }


def main():
    points = [
        (5, 3), (5, 4),
        (6, 3), (6, 4), (6, 5),
        (7, 3), (7, 4), (7, 5), (7, 6),
        (8, 3), (8, 4), (8, 5),
    ]

    print(f"{'n':<3}{'k':<3}{'ms':<22}{'P':<6}"
          f"{'cycles':<8}{'|SK|':<7}{'e/proc':<8}{'|E_proj|':<10}"
          f"{'ham_len':<10}{'time':<8}")
    print("-" * 85)

    rows = []
    for (n, k) in points:
        r = run_point(n, k)
        rows.append(r)
        print(f"{r['n']:<3}{r['k']:<3}{str(r['ms']):<22}{r['P']:<6}"
              f"{r['cycles']:<8}{str(r['sk']):<7}"
              f"{str(r['edges_per_proc']):<8}{str(r['distinct_edges']):<10}"
              f"{str(r['ham']):<10}{r['elapsed']:.1f}")

    print("\n" + "=" * 70)
    print("BINARY-COUNT INVARIANCE CHECK (at fixed n)")
    print("=" * 70)
    by_n = defaultdict(list)
    for r in rows:
        if r["sk"] is not None:
            by_n[r["n"]].append(r)
    for n in sorted(by_n):
        sks = set(r["sk"] for r in by_n[n])
        epps = set(r["edges_per_proc"] for r in by_n[n])
        ks = [r["k"] for r in by_n[n]]
        invariant = "YES" if len(sks) == 1 and len(epps) == 1 else "NO"
        print(f"  n={n}: k values {ks}, |SK| set {sks}, e/proc set {epps}  "
              f"invariant={invariant}")

    print("\n" + "=" * 70)
    print("DISTINCT PROJECTION EDGES  |E_proj|(n, k)")
    print("=" * 70)
    print(f"{'':<4}", end="")
    for k in [3, 4, 5, 6]:
        print(f"k={k:<8}", end="")
    print()
    for n in [5, 6, 7, 8]:
        print(f"n={n:<2}", end="")
        for k in [3, 4, 5, 6]:
            val = None
            for r in rows:
                if r["n"] == n and r["k"] == k and r["distinct_edges"] is not None:
                    val = r["distinct_edges"]
                    break
            print(f"{str(val) if val else '-':<10}", end="")
        print()

    print("\n  (values depend on k, independent of n for fixed k)")

    print("\n" + "=" * 70)
    print("HAMILTONIAN CYCLE IN SK MIDDLE LAYER")
    print("=" * 70)
    for r in rows:
        if r["ham"] is not None:
            print(f"  n={r['n']} k={r['k']}: middle-layer Hamilton = {r['ham']}")


if __name__ == "__main__":
    main()
