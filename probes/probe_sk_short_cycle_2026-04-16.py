#!/usr/bin/env python3
"""Shortest directed cycle in the forced NG graph.

For each record, build the directed graph G on VC-NG where edges are
forced moves (c → c' with c' ∈ VC-NG). Find the shortest directed cycle.

Tests:
  S1: Does a directed cycle always exist? (yes, by SK.Nonempty)
  S2: Shortest directed cycle length distribution.
  S3: Is the shortest cycle always ≤ L (cycle length)?
  S4: Is the shortest cycle always ≤ 2n?
  S5: Distribution of cycle lengths — are short cycles (2, 3) common?

A length-k directed cycle gives an immediate self-map f(c) = next config.
Short cycles → tight Lean construction.
"""
from itertools import product as iproduct
from collections import defaultdict, deque, Counter
import time


def m_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
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


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])
    return V


def shortest_cycle(nodes, adj, max_len):
    """BFS-based shortest cycle search; returns length of shortest or None."""
    best = None
    for src in nodes:
        # BFS from src, looking for an edge back to src
        dist = {src: 0}
        q = deque([src])
        while q:
            u = q.popleft()
            if best is not None and dist[u] >= best:
                continue
            for v in adj.get(u, []):
                if v == src:
                    cyc_len = dist[u] + 1
                    if best is None or cyc_len < best:
                        best = cyc_len
                    continue
                if v not in dist and dist[u] + 1 < max_len:
                    dist[v] = dist[u] + 1
                    q.append(v)
        if best is not None and best <= 2:
            return best  # can't get shorter than 2
    return best


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    adj = defaultdict(list)
    edges = 0
    for c in VC_NG:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                v = move_entries[ctx]
                nc = list(c); nc[p] = v; nc = tuple(nc)
                if nc in VC_NG:
                    adj[c].append(nc)
                    edges += 1

    # Shortest cycle — bounded by 2n
    scl = shortest_cycle(VC_NG, adj, max_len=2 * n + 2)
    return {
        'n': n, 'ms': ms, 'L': L,
        'VC_NG_size': len(VC_NG),
        'edges': edges,
        'shortest_cycle': scl,
    }


def main():
    print("=" * 72)
    print("Shortest directed cycle in NG forced graph")
    print("=" * 72)
    plan = [
        (5, 2, 80, 3.0, 16),
        (6, 5, 25, 3.0, 17),
        (7, 30, 10, 4.0, 17),
        (8, 300, 5, 15.0, 20),
    ]
    all_records = []
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets  L_max={L_max} ===", flush=True)
        t0 = time.time()
        count = 0
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n + 2:
                    continue
                r = analyze(ms, n, cycle, movers, det)
                all_records.append(r)
                count += 1
            if (idx + 1) % max(1, len(sampled) // 10) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}")
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        if not recs: continue
        have_cycle = sum(1 for r in recs if r['shortest_cycle'] is not None)
        lengths = [r['shortest_cycle'] for r in recs if r['shortest_cycle'] is not None]
        nil = sum(1 for r in recs if r['shortest_cycle'] is None)
        print(f"\n  n={n}  records={len(recs)}")
        print(f"    has directed cycle ≤ 2n+2:  {have_cycle}/{len(recs)} ({100*have_cycle/len(recs):.1f}%)")
        if lengths:
            ld = Counter(lengths)
            print(f"    shortest cycle length dist: {dict(sorted(ld.items()))}")
            print(f"    min={min(lengths)}  max={max(lengths)}  avg={sum(lengths)/len(lengths):.1f}")
        if nil:
            print(f"    no cycle found within 2n+2: {nil}")


if __name__ == "__main__":
    main()
