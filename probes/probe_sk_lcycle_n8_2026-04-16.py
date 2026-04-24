#!/usr/bin/env python3
"""Does shortest cycle in peel(N_1) have length exactly L at n=8?

Previous result: 641/641 at n=5,6,7 shortest-cycle-in-peel = L.
At n=8, |peel| min = 84 < 128 = 2^(n-1), so the n=7 exact theorem breaks.
But the L-cycle might still hold.

Cheaper: just check shortest cycle length vs L at n=8.
"""
from itertools import product as iproduct
from collections import defaultdict, deque
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


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    cycle_set = set(cycle)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    N1 = set()
    for c in cycle:
        for q in range(n):
            for v in range(ms[q]):
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
    cur = set(N1)
    while True:
        to_remove = {c for c in cur if not any(s in cur for s in adj[c])}
        if not to_remove: break
        cur -= to_remove
    peel = cur
    if not peel: return None
    # Shortest cycle via BFS
    shortest = None
    # Try each node as start (limit to first K for speed)
    for src in list(peel)[:min(20, len(peel))]:
        dist = {src: 0}
        q = deque([src])
        while q:
            u = q.popleft()
            if shortest is not None and dist[u] >= shortest:
                break
            for v in adj[u]:
                if v not in peel: continue
                if v == src:
                    cyc_len = dist[u] + 1
                    if shortest is None or cyc_len < shortest:
                        shortest = cyc_len
                    continue
                if v not in dist:
                    dist[v] = dist[u] + 1
                    q.append(v)
    return {
        'n': n, 'L': L, 'peel_size': len(peel), 'shortest': shortest,
    }


def main():
    print("=" * 72, flush=True)
    print("Shortest cycle in peel(N_1) at n=8?", flush=True)
    print("=" * 72, flush=True)
    records = []
    tb = 6.0; max_cycles = 3; L_max = 19
    n = 8
    Mn = m_n_sharp(n)
    multisets = enumerate_multisets(n, Mn)
    sampled = multisets[::160]  # sparser, n=8 is expensive
    print(f"n=8  {len(sampled)} multisets", flush=True)
    t0 = time.time()
    for idx, ms in enumerate(sampled):
        cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
        for cycle, movers, det in cycles:
            L = len(movers)
            if L < 2 * n + 2: continue
            r = analyze(ms, n, cycle, movers, det)
            if r is None: continue
            records.append(r)
        if (idx + 1) % max(1, len(sampled) // 6) == 0 or idx == len(sampled) - 1:
            print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={len(records)}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}")
    print(f"Total records: {len(records)}")
    eq_L = sum(1 for r in records if r['shortest'] == r['L'])
    print(f"shortest == L: {eq_L}/{len(records)}")
    lt_L = sum(1 for r in records if r['shortest'] is not None and r['shortest'] < r['L'])
    gt_L = sum(1 for r in records if r['shortest'] is not None and r['shortest'] > r['L'])
    print(f"shortest < L: {lt_L}/{len(records)}")
    print(f"shortest > L: {gt_L}/{len(records)}")
    none_ct = sum(1 for r in records if r['shortest'] is None)
    print(f"no cycle found: {none_ct}/{len(records)}")
    # Show a few examples
    print("\nSample records:")
    for r in records[:8]:
        print(f"  L={r['L']}  shortest={r['shortest']}  |peel|={r['peel_size']}")


if __name__ == "__main__":
    main()
