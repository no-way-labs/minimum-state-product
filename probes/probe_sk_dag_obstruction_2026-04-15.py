#!/usr/bin/env python3
"""DAG obstruction probe: what structural property of the forced graph
prevents it from being a DAG at sub-M_n?

If the forced graph WERE a DAG, it would have a topological ordering.
Every vertex would have a "rank" (longest path from any source).
The DAG's depth = max rank.

This probe computes, for each cycle at sub-M_n:
1. The actual DAG depth of the forced graph AFTER SK removal
   (the "peeled" graph IS a DAG — the part that gets removed).
2. How many rounds of sink-removal it takes to stabilize.
3. The edge-to-vertex ratio at each removal round.
4. At what round the graph "stabilizes" (stops losing vertices)
   — this is when we've found SK.
5. KEY: the "obstruction signature" — at the moment the peeling
   stops, what's the in-degree and out-degree distribution of
   remaining (SK) vertices? What makes them immune to peeling?
6. For each SK vertex, how many of its forced out-edges stay in SK
   vs go outside SK? If ALL edges stay in SK, the vertex is deeply
   embedded. If just 1 edge stays, it's barely surviving.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time

def m_n_sharp(n):
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)

def enumerate_multisets(n, max_product):
    out = []
    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product:
                out.append(tuple(prefix))
            return
        for m in range(2, max_product + 1):
            new_prod = prod * m
            min_remaining = 2 ** (n - i - 1)
            if new_prod * min_remaining >= max_product:
                break
            prefix.append(m)
            rec(i + 1, prefix, new_prod)
            prefix.pop()
    rec(0, [], 1)
    return out

def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen_cycles = set()
    t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)):
                return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max:
            return
        for p in range(n):
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp)
            forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp:
                    continue
                if forced_out is not None and forced_out != new_val:
                    continue
                new_det = dict(det)
                new_det[km] = new_val
                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        ok = False; break
                    new_det[ki] = Si
                if not ok:
                    continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path):
                    continue
                dfs(start, nc, new_det, path + [nc], movers + [p])
    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            break
        dfs(start, start, {}, [start], [])
    return found


def analyze_peeling(ms, n, cycle, det):
    """Detailed analysis of the iterative sink-removal process."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycle_set = set(cycle)
    ng = [c for c in all_configs if c not in cycle_set]
    ng_set = set(ng)

    # Build forced graph
    adj = defaultdict(list)  # out-edges
    in_adj = defaultdict(list)  # in-edges
    for c in ng:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c); nc[p] = det[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append(nc)
                    in_adj[nc].append(c)

    # Iterative sink removal with per-round statistics
    remaining = set(ng)
    rounds = []
    while True:
        # Count out-degree within remaining for each vertex
        sinks = set()
        out_degrees = Counter()
        for c in remaining:
            od = sum(1 for tgt in adj.get(c, []) if tgt in remaining)
            out_degrees[od] += 1
            if od == 0:
                sinks.add(c)
        if not sinks:
            break
        rounds.append({
            'remaining': len(remaining),
            'sinks_removed': len(sinks),
            'out_degree_dist': dict(out_degrees),
        })
        remaining -= sinks

    sk = remaining
    sk_size = len(sk)

    # SK vertex analysis: out-degree within SK, positions of out-edges
    sk_out_degrees = Counter()
    sk_positions_used = Counter()  # which positions p provide the surviving edges
    min_sk_outdeg = float('inf')
    for c in sk:
        od = 0
        for tgt in adj.get(c, []):
            if tgt in sk:
                od += 1
        sk_out_degrees[od] += 1
        if od < min_sk_outdeg:
            min_sk_outdeg = od
        # Which positions provide edges within SK?
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c); nc[p] = det[key]; nc = tuple(nc)
                if nc in sk:
                    sk_positions_used[p] += 1

    return {
        'ng_size': len(ng),
        'sk_size': sk_size,
        'num_rounds': len(rounds),
        'rounds': rounds,
        'sk_out_degrees': dict(sk_out_degrees),
        'min_sk_outdeg': min_sk_outdeg if sk else 0,
        'sk_positions_used': dict(sk_positions_used),
    }


def main():
    print("=" * 72, flush=True)
    print("DAG obstruction probe: peeling analysis of forced graph", flush=True)
    print("=" * 72, flush=True)

    plan = [
        (5, 1, 1500, 5.0, 15),
        (6, 4, 500, 3.0, 17),
    ]

    # Aggregation
    by_nL = defaultdict(list)

    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n:
                    continue
                result = analyze_peeling(ms, n, cycle, det)
                by_nL[(n, L)].append(result)
            if (idx + 1) % 10 == 0 or idx == len(sampled) - 1:
                elapsed = time.time() - t0
                print(f"  [{idx+1}/{len(sampled)}]  {elapsed:.0f}s", flush=True)

    print(f"\n{'='*72}", flush=True)
    print(f"=== Peeling statistics ===", flush=True)
    print(f"  n  L   count  avg_rounds  avg_sk  min_sk  "
          f"avg_min_outdeg  positions_used", flush=True)
    for (n, L) in sorted(by_nL.keys()):
        results = by_nL[(n, L)]
        avg_rounds = sum(r['num_rounds'] for r in results) / len(results)
        avg_sk = sum(r['sk_size'] for r in results) / len(results)
        min_sk = min(r['sk_size'] for r in results)
        avg_min_od = sum(r['min_sk_outdeg'] for r in results) / len(results)
        # Most common positions used
        pos_agg = Counter()
        for r in results:
            for p, cnt in r['sk_positions_used'].items():
                pos_agg[p] += cnt
        top_pos = pos_agg.most_common(3)
        print(f"  {n}  {L:2d}  {len(results):5d}  {avg_rounds:10.1f}  "
              f"{avg_sk:6.1f}  {min_sk:5d}  "
              f"{avg_min_od:14.2f}  {top_pos}", flush=True)

    # SK out-degree distribution (aggregated)
    print(f"\n=== SK out-degree distribution (aggregated across all cycles) ===",
          flush=True)
    for (n, L) in sorted(by_nL.keys()):
        if L != 2 * n + 2 and L != 2 * n:
            continue
        od_agg = Counter()
        for r in by_nL[(n, L)]:
            for od, cnt in r['sk_out_degrees'].items():
                od_agg[od] += cnt
        total = sum(od_agg.values())
        if total == 0:
            continue
        print(f"  n={n}  L={L}:", flush=True)
        for od in sorted(od_agg.keys()):
            pct = 100 * od_agg[od] / total
            print(f"    out-degree {od}: {od_agg[od]} ({pct:.1f}%)", flush=True)

    # Round-by-round profile for a sample
    print(f"\n=== Sample peeling profile (first cycle at each n, L=2n) ===",
          flush=True)
    for (n, L) in sorted(by_nL.keys()):
        if L != 2 * n:
            continue
        results = by_nL[(n, L)]
        if not results:
            continue
        r = results[0]
        print(f"  n={n}  L={L}  |NG|={r['ng_size']}  |SK|={r['sk_size']}  "
              f"rounds={r['num_rounds']}", flush=True)
        for i, rd in enumerate(r['rounds'][:10]):
            print(f"    round {i}: remaining={rd['remaining']}  "
                  f"removed={rd['sinks_removed']}  "
                  f"od_dist={rd['out_degree_dist']}", flush=True)


if __name__ == "__main__":
    main()
