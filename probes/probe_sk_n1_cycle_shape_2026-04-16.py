#!/usr/bin/env python3
"""Find shortest directed cycle entirely within N_1(C) ∩ VC_NG.

If peel(N_1) nonempty, there's a cycle in N_1. What's its shape?
  S1: shortest cycle length distribution
  S2: does the shortest cycle relate to L (= 2n+2 or the actual cycle length)?
  S3: how many distinct cycles in peel(N_1)?
  S4: do cycle configs have common (q, v, i) form?
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


def shortest_cycle_in(T, adj):
    best = None
    for src in T:
        if best is not None and best <= 2: break
        dist = {src: 0}
        q = deque([src])
        while q:
            u = q.popleft()
            if best is not None and dist[u] + 1 >= best: continue
            for v in adj[u]:
                if v == src:
                    cl = dist[u] + 1
                    if best is None or cl < best: best = cl
                    continue
                if v not in dist and v in T:
                    dist[v] = dist[u] + 1
                    q.append(v)
    return best


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    N1 = set()
    for c in cycle:
        for q in range(n):
            for v in V[q]:
                if v == c[q]: continue
                nc = list(c); nc[q] = v; nc = tuple(nc)
                if nc not in cycle_set:
                    N1.add(nc)

    adj = defaultdict(list)
    for c in N1:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                val = move_entries[ctx]
                nc = list(c); nc[p] = val; nc = tuple(nc)
                if nc in N1:
                    adj[c].append(nc)

    # Peel
    cur = set(N1)
    while True:
        to_remove = {c for c in cur if not any(s in cur for s in adj[c])}
        if not to_remove: break
        cur -= to_remove
    peel_set = cur

    if not peel_set:
        return {'n': n, 'ms': ms, 'L': L, 'peel_empty': True}

    # Restrict adj to peel
    peel_adj = defaultdict(list)
    for c in peel_set:
        for s in adj[c]:
            if s in peel_set:
                peel_adj[c].append(s)

    # Shortest cycle in peel
    scyc = shortest_cycle_in(peel_set, peel_adj)

    return {
        'n': n, 'ms': ms, 'L': L,
        'peel_empty': False,
        'peel_size': len(peel_set),
        'shortest_cycle_in_peel': scyc,
    }


def main():
    print("=" * 72, flush=True)
    print("Shortest cycle in peel(N_1(C))", flush=True)
    print("=" * 72, flush=True)
    plan = [
        (5, 3, 40, 3.0, 16),
        (6, 8, 15, 3.0, 17),
        (7, 40, 8, 3.0, 17),
    ]
    all_records = []
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===", flush=True)
        t0 = time.time()
        count = 0
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n + 2: continue
                r = analyze(ms, n, cycle, movers, det)
                all_records.append(r)
                count += 1
            if (idx + 1) % max(1, len(sampled) // 10) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}", flush=True)
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        if not recs: continue
        valid = [r for r in recs if not r['peel_empty']]
        print(f"\n  n={n}  records={len(recs)} (peel nonempty: {len(valid)})")
        sc = [r['shortest_cycle_in_peel'] for r in valid if r['shortest_cycle_in_peel']]
        if sc:
            sd = Counter(sc)
            print(f"    shortest cycle in peel: min={min(sc)} max={max(sc)} avg={sum(sc)/len(sc):.1f}")
            print(f"    distribution: {dict(sorted(sd.items()))}")
        # vs L
        c_vs_L = [(r['shortest_cycle_in_peel'], r['L']) for r in valid if r['shortest_cycle_in_peel']]
        eq_L = sum(1 for a, b in c_vs_L if a == b)
        lt_L = sum(1 for a, b in c_vs_L if a < b)
        print(f"    cycle == L: {eq_L}/{len(c_vs_L)} ({100*eq_L/len(c_vs_L):.1f}%)")
        print(f"    cycle < L: {lt_L}/{len(c_vs_L)} ({100*lt_L/len(c_vs_L):.1f}%)")


if __name__ == "__main__":
    main()
