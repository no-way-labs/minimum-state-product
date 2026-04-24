#!/usr/bin/env python3
"""Is distance-2 slab pair always sufficient?

For each record, for each distance d ∈ {1, 2, 3, ...}, compute
  best_d := max over q1 and v1 ∈ V_{q1}, v2 ∈ V_{q1+d} of
           |Slab(q1, v1) ∪ Slab(q1+d, v2)|.

Tests:
  D1: Is best_2 ≥ 2^(n-1) universally?
  D2: What's the max distance d such that best_d ≥ 2^(n-1) holds universally?
  D3: Distribution of WHICH distance gives the max union.
  D4: Within distance-2 pairs, is there a preferred (v1, v2) pattern?
  D5: Does best_d grow with d? Or peak at d=2?
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

    # For each distance d = 1..n//2, compute best over (q1, v1, v2):
    best_by_d = {}
    opt_by_d = {}
    for d in range(1, n // 2 + 1):
        best = 0
        best_witness = None
        for q1 in range(n):
            q2 = (q1 + d) % n
            for v1 in V[q1]:
                s1 = slab[(q1, v1)]
                for v2 in V[q2]:
                    s2 = slab[(q2, v2)]
                    u = len(s1 | s2)
                    if u > best:
                        best = u
                        best_witness = (q1, v1, q2, v2)
        best_by_d[d] = best
        opt_by_d[d] = best_witness

    # Single-slab best
    single_best = max(len(s) for s in slab.values())

    # Which distance gives the max?
    arg_max_d = max(best_by_d, key=best_by_d.get)

    # Do all of d=1..n//2 satisfy bound?
    satisfies = {d: (best_by_d[d] >= bound) for d in best_by_d}

    return {
        'n': n, 'ms': ms, 'L': L,
        'SK_size': len(SK),
        'bound': bound,
        'single_best': single_best,
        'single_ge': single_best >= bound,
        'best_by_d': best_by_d,
        'satisfies': satisfies,
        'arg_max_d': arg_max_d,
    }


def main():
    print("=" * 72)
    print("Fixed-distance slab pair probe — which d suffices?")
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
        print(f"\n  n={n}  records={len(recs)}  bound=2^(n-1)={bound}")
        single_ge = sum(1 for r in recs if r['single_ge'])
        print(f"    single slab ≥ bound:  {single_ge}/{len(recs)} ({100*single_ge/len(recs):.1f}%)")
        for d in range(1, n // 2 + 1):
            count = sum(1 for r in recs if r['satisfies'][d])
            avg = sum(r['best_by_d'][d] for r in recs) / len(recs)
            min_d = min(r['best_by_d'][d] for r in recs)
            print(f"    best pair d={d} ≥ bound:  {count}/{len(recs)} ({100*count/len(recs):.1f}%)  min={min_d}  avg={avg:.1f}")
        arg_max_dist = Counter(r['arg_max_d'] for r in recs)
        print(f"    arg-max d distribution: {dict(arg_max_dist.most_common())}")


if __name__ == "__main__":
    main()
