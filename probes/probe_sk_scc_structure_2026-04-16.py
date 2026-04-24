#!/usr/bin/env python3
"""SCC structural analysis: what does a non-trivial SCC of NG look like?

For each record, find non-trivial SCCs in the forced NG-graph.
Analyze:
  S1: # SCCs and their sizes
  S2: For largest non-trivial SCC: distribution of min-Hamming-to-C
  S3: Is the SCC = peel(N_k(C)) for some k?
  S4: Are all configs in SCC at bounded Hamming distance from C?
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time, sys


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


def tarjan_scc(nodes, adj):
    index = {}; low = {}
    stack = []; on_stack = set()
    counter = [0]; sccs = []
    sys.setrecursionlimit(200000)
    def strong(v):
        index[v] = counter[0]; low[v] = counter[0]; counter[0] += 1
        stack.append(v); on_stack.add(v)
        for w in adj.get(v, []):
            if w not in index:
                strong(w); low[v] = min(low[v], low[w])
            elif w in on_stack:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop(); on_stack.discard(w)
                comp.append(w)
                if w == v: break
            sccs.append(comp)
    for v in nodes:
        if v not in index: strong(v)
    return sccs


def hamming(a, b, n):
    return sum(1 for i in range(n) if a[i] != b[i])


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    adj = defaultdict(list)
    for c in VC_NG:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                v = move_entries[ctx]
                nc = list(c); nc[p] = v; nc = tuple(nc)
                if nc in VC_NG:
                    adj[c].append(nc)
    sccs = tarjan_scc(list(VC_NG), adj)
    nontriv = [c for c in sccs if len(c) >= 2 or (len(c) == 1 and c[0] in adj.get(c[0], []))]
    nontriv.sort(key=len, reverse=True)

    if not nontriv:
        return {
            'n': n, 'ms': ms, 'L': L,
            'has_nontriv': False,
        }

    largest = nontriv[0]
    # Hamming distribution
    hd_cnt = Counter()
    for c in largest:
        hd = min(hamming(c, cc, n) for cc in cycle)
        hd_cnt[hd] += 1
    max_hd = max(hd_cnt.keys())

    return {
        'n': n, 'ms': ms, 'L': L,
        'has_nontriv': True,
        'num_nontriv': len(nontriv),
        'largest_size': len(largest),
        'nontriv_sizes': [len(c) for c in nontriv],
        'largest_hd_dist': dict(hd_cnt),
        'largest_max_hd': max_hd,
    }


def main():
    print("=" * 72, flush=True)
    print("SCC structure probe", flush=True)
    print("=" * 72, flush=True)
    plan = [
        (5, 3, 40, 3.0, 16),
        (6, 8, 15, 3.0, 17),
        (7, 40, 8, 3.0, 17),
        (8, 500, 3, 12.0, 20),
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
        has = sum(1 for r in recs if r['has_nontriv'])
        print(f"\n  n={n}  records={len(recs)}")
        print(f"    has non-trivial SCC: {has}/{len(recs)} ({100*has/len(recs):.1f}%)")
        with_scc = [r for r in recs if r['has_nontriv']]
        if with_scc:
            ls = [r['largest_size'] for r in with_scc]
            mh = [r['largest_max_hd'] for r in with_scc]
            print(f"    largest SCC size: min={min(ls)} max={max(ls)} avg={sum(ls)/len(ls):.1f}")
            print(f"    largest SCC max_hd: min={min(mh)} max={max(mh)} avg={sum(mh)/len(mh):.1f}")
            hd_dists = Counter()
            for r in with_scc:
                for h, c in r['largest_hd_dist'].items():
                    hd_dists[h] += c
            print(f"    total hd distribution in largest SCCs: {dict(sorted(hd_dists.items()))}")


if __name__ == "__main__":
    main()
