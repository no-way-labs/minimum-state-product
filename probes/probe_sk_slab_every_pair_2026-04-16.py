#!/usr/bin/env python3
"""Every-pair slab-union test.

For each record, for each (q1, q2) with q1 < q2, compute
  f(q1, q2) := max over (v1 ∈ V_{q1}, v2 ∈ V_{q2}) of |Slab(q1,v1) ∪ Slab(q2,v2)|.

Test: is min over (q1, q2) of f(q1, q2) still ≥ 2^(n-1)?

Also compute per-position max-slab:
  g(q) := max over v ∈ V_q of |Slab(q, v)|
Check: is min_q g(q) ≥ 2^(n-2)?
"""
from itertools import product as iproduct, combinations
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


def compute_sk(vcng_set, move_entries, n):
    current = set(vcng_set)
    while True:
        victims = set()
        for c in current:
            has_forced = False
            for p in range(n):
                ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
                if ctx in move_entries:
                    v = move_entries[ctx]
                    nc = list(c); nc[p] = v; nc = tuple(nc)
                    if nc in current:
                        has_forced = True
                        break
            if not has_forced:
                victims.add(c)
        if not victims:
            break
        current -= victims
    return current


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    SK = compute_sk(VC_NG, move_entries, n)

    slab = {}
    for q in range(n):
        for v in V[q]:
            slab[(q, v)] = {c for c in SK if c[q] == v}

    bound = 2 ** (n - 1)
    bound2 = 2 ** (n - 2)

    # Per-position max slab
    g = {q: max(len(slab[(q, v)]) for v in V[q]) for q in range(n)}
    min_g = min(g.values())

    # Every-pair max union
    pair_max = {}
    for q1, q2 in combinations(range(n), 2):
        best = 0
        for v1 in V[q1]:
            s1 = slab[(q1, v1)]
            for v2 in V[q2]:
                u = len(s1 | slab[(q2, v2)])
                if u > best: best = u
        pair_max[(q1, q2)] = best
    min_pair = min(pair_max.values())
    max_pair = max(pair_max.values())

    # For each pair: fraction of (v1, v2) combos achieving bound
    return {
        'n': n, 'ms': ms, 'L': L,
        'SK_size': len(SK),
        'bound': bound,
        'bound2': bound2,
        'min_g': min_g,
        'min_g_ge_bound2': min_g >= bound2,
        'min_pair': min_pair,
        'min_pair_ge_bound': min_pair >= bound,
        'max_pair': max_pair,
    }


def main():
    print("=" * 72)
    print("Every-pair slab union — is min_{(q1,q2)} max_{v1,v2} |S ∪ S| ≥ 2^(n-1)?")
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
        bound = 2 ** (n - 1)
        bound2 = 2 ** (n - 2)
        mg = sum(1 for r in recs if r['min_g_ge_bound2'])
        mp = sum(1 for r in recs if r['min_pair_ge_bound'])
        min_mg = min(r['min_g'] for r in recs)
        avg_mg = sum(r['min_g'] for r in recs) / len(recs)
        min_mp = min(r['min_pair'] for r in recs)
        avg_mp = sum(r['min_pair'] for r in recs) / len(recs)
        max_mp = max(r['max_pair'] for r in recs)
        print(f"\n  n={n}  records={len(recs)}  2^(n-1)={bound}  2^(n-2)={bound2}")
        print(f"    min_q g(q) ≥ 2^(n-2):   {mg}/{len(recs)} ({100*mg/len(recs):.1f}%)  min={min_mg} avg={avg_mg:.1f}")
        print(f"    EVERY pair ≥ 2^(n-1):   {mp}/{len(recs)} ({100*mp/len(recs):.1f}%)  min={min_mp} avg={avg_mp:.1f} max={max_mp}")


if __name__ == "__main__":
    main()
