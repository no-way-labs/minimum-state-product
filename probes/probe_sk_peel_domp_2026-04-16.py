#!/usr/bin/env python3
"""Test: peel(N_1) = N_1 restricted to dominant-pair anchors?

Define dom_pair(q) = 2 values of V_q with longest total residence time
(ties broken by lex order or whatever gives stable set).

N_1^dom_all = {c_i[q←v] ∈ N_1 : EVERY anchor (q,v) of c has v ∈ dom_pair(q)}

Test at n=5,6,7:
  - peel = N_1^dom_all?
  - |N_1^dom_all| = |peel|?
  - N_1^dom_all closed under forced NG-successor?
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


def residence_times(cycle, n):
    """For each q, total time spent at each value."""
    L = len(cycle)
    times = [defaultdict(int) for _ in range(n)]
    for c in cycle:
        for q in range(n):
            times[q][c[q]] += 1
    return times


def dom_pair(times_q):
    """Top-2 values by residence time. Ties broken lex."""
    items = sorted(times_q.items(), key=lambda kv: (-kv[1], kv[0]))
    if len(items) < 2:
        return set(kv[0] for kv in items)
    return {items[0][0], items[1][0]}


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    times = residence_times(cycle, n)
    dom = [dom_pair(times[q]) for q in range(n)]

    # N_1
    N1_anchors = defaultdict(list)
    N1 = set()
    for c in cycle:
        for q in range(n):
            for v in range(ms[q]):
                if v == c[q]: continue
                nc = list(c); nc[q] = v; nc = tuple(nc)
                if nc not in cycle_set:
                    N1.add(nc)
                    N1_anchors[nc].append((q, v))

    N1_dom_all = set()
    for nc, anchors in N1_anchors.items():
        if all(v in dom[q] for (q, v) in anchors):
            N1_dom_all.add(nc)

    # Also any: at least one anchor is dom
    N1_dom_any = set()
    for nc, anchors in N1_anchors.items():
        if any(v in dom[q] for (q, v) in anchors):
            N1_dom_any.add(nc)

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

    # Closure tests
    all_closed = all(any(s in N1_dom_all for s in adj[c]) for c in N1_dom_all)
    any_closed = all(any(s in N1_dom_any for s in adj[c]) for c in N1_dom_any)

    return {
        'n': n, 'ms': ms, 'L': L,
        'peel_size': len(peel),
        'N1_dom_all_size': len(N1_dom_all),
        'N1_dom_any_size': len(N1_dom_any),
        'peel_eq_dom_all': peel == N1_dom_all,
        'peel_sub_dom_all': peel <= N1_dom_all,
        'peel_sup_dom_all': peel >= N1_dom_all,
        'all_closed': all_closed,
        'any_closed': any_closed,
    }


def main():
    print("=" * 72, flush=True)
    print("peel = N_1 restricted to dominant-pair anchors?", flush=True)
    print("=" * 72, flush=True)
    plan = [
        (5, 3, 40, 3.0, 16),
        (6, 8, 15, 3.0, 17),
        (7, 40, 8, 4.0, 17),
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
                if r is None: continue
                all_records.append(r)
                count += 1
            if (idx + 1) % max(1, len(sampled) // 5) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}", flush=True)
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        if not recs: continue
        print(f"\n  n={n}  records={len(recs)}")
        ps = [r['peel_size'] for r in recs]
        das = [r['N1_dom_all_size'] for r in recs]
        print(f"    |peel|: min={min(ps)} max={max(ps)} avg={sum(ps)/len(ps):.1f}")
        print(f"    |N_1^dom_all|: min={min(das)} max={max(das)} avg={sum(das)/len(das):.1f}")
        for flag in ['peel_eq_dom_all', 'peel_sub_dom_all', 'peel_sup_dom_all', 'all_closed', 'any_closed']:
            cnt = sum(1 for r in recs if r[flag])
            print(f"    {flag}: {cnt}/{len(recs)} ({100*cnt/len(recs):.1f}%)")


if __name__ == "__main__":
    main()
