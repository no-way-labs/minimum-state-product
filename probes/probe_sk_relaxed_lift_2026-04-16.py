#!/usr/bin/env python3
"""Relaxed lift: walk follows any forced NG-move (not just lift from C).

For each record, for each start (q, v, i) with c_i[q<-v] in N_1(C):
  Walk forward: at each step, pick ANY forced NG-neighbor of current
  config (not just the one matching c_{i+j+1}'s firing position).
  Track Hamming distance to nearest cycle config.
  See if walk returns to start within 2L steps.

Multiple successor choices: DFS up to a bounded depth.

Measure:
  R1: ∃ start with a closed walk (returning within 2L)?
  R2: Max Hamming distance to cycle reached during walk.
  R3: Distribution of closed-walk lengths.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
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


def hamming(a, b, n):
    return sum(1 for i in range(n) if a[i] != b[i])


def min_hamming_to_cycle(c, cycle, n):
    return min(hamming(c, cc, n) for cc in cycle)


def forced_neighbors_in_ng(c, move_entries, n, VC_NG):
    res = []
    for p in range(n):
        ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
        if ctx in move_entries:
            v = move_entries[ctx]
            nc = list(c); nc[p] = v; nc = tuple(nc)
            if nc in VC_NG:
                res.append(nc)
    return res


def find_closed_walk(start, VC_NG, move_entries, n, cycle, max_steps):
    """DFS for a closed walk from start. Returns (found, max_hd) or (False, -1)."""
    best_max_hd = 0
    # DFS with bounded depth
    from sys import setrecursionlimit
    setrecursionlimit(100000)
    cache = {}
    def dfs(c, depth, max_hd):
        nonlocal best_max_hd
        if depth > 0 and c == start:
            if max_hd > best_max_hd: best_max_hd = max_hd
            return depth
        if depth >= max_steps:
            return None
        # iterative deepening; too expensive in full, so use BFS instead
        return None

    # Use BFS to find shortest cycle through `start`
    # Build adjacency list on-the-fly
    adj = {}
    def get_adj(c):
        if c not in adj:
            adj[c] = forced_neighbors_in_ng(c, move_entries, n, VC_NG)
        return adj[c]

    # BFS: dist[c] = shortest distance from start, with predecessor tracking
    from collections import deque
    dist = {start: 0}
    max_hd = {start: min_hamming_to_cycle(start, cycle, n)}
    q = deque([start])
    found_len = None
    while q:
        u = q.popleft()
        if dist[u] >= max_steps:
            continue
        for v in get_adj(u):
            if v == start:
                if found_len is None or dist[u] + 1 < found_len:
                    found_len = dist[u] + 1
                continue
            if v not in dist:
                dist[v] = dist[u] + 1
                hd = min_hamming_to_cycle(v, cycle, n)
                max_hd[v] = max(max_hd[u], hd)
                q.append(v)
    if found_len is None:
        return False, -1
    # Compute max hd reached among nodes within found_len of start
    reach_hd = max(max_hd[c] for c in dist if dist[c] <= found_len)
    return True, reach_hd, found_len


def analyze(ms, n, cycle, movers, det, max_starts=10, max_steps=30):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    # Collect candidate starts in N_1(C)
    N1 = []
    for i, c in enumerate(cycle):
        for q in range(n):
            for v in V[q]:
                if v == c[q]: continue
                nc = list(c); nc[q] = v; nc = tuple(nc)
                if nc in VC_NG:
                    N1.append(nc)
    # Dedup
    N1 = list(set(N1))

    # Try up to max_starts starts; look for closed walk
    found_any = False
    best_len = None
    max_hd_seen = 0
    for start in N1[:max_starts]:
        r = find_closed_walk(start, VC_NG, move_entries, n, cycle, max_steps)
        if r[0]:
            found_any = True
            _, hd, length = r
            if best_len is None or length < best_len: best_len = length
            max_hd_seen = max(max_hd_seen, hd)
    return {
        'n': n, 'ms': ms, 'L': L,
        'N1_size': len(N1),
        'any_closed': found_any,
        'best_len': best_len,
        'max_hd_reached': max_hd_seen,
    }


def main():
    print("=" * 72)
    print("Relaxed-lift probe: closed walk from N_1(C), any forced NG-path", flush=True)
    print("=" * 72)
    plan = [
        (5, 3, 30, 3.0, 16),
        (6, 8, 10, 3.0, 17),
        (7, 40, 5, 3.0, 17),
        (8, 500, 3, 10.0, 20),
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
                r = analyze(ms, n, cycle, movers, det,
                            max_starts=8, max_steps=min(3 * L, 60))
                all_records.append(r)
                count += 1
            if (idx + 1) % max(1, len(sampled) // 10) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}", flush=True)
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        if not recs: continue
        any_c = sum(1 for r in recs if r['any_closed'])
        lens = [r['best_len'] for r in recs if r['best_len'] is not None]
        hds = [r['max_hd_reached'] for r in recs if r['any_closed']]
        print(f"\n  n={n}  records={len(recs)}")
        print(f"    ∃ closed walk from N_1 start (within 3L): {any_c}/{len(recs)} ({100*any_c/len(recs):.1f}%)")
        if lens:
            print(f"    closed walk len: min={min(lens)} max={max(lens)} avg={sum(lens)/len(lens):.1f}")
            lc = Counter(lens)
            print(f"    length distribution (top 5): {dict(lc.most_common(5))}")
        if hds:
            print(f"    max Hamming distance reached: min={min(hds)} max={max(hds)} avg={sum(hds)/len(hds):.1f}")
            hc = Counter(hds)
            print(f"    max-hd distribution: {dict(hc.most_common())}")


if __name__ == "__main__":
    main()
