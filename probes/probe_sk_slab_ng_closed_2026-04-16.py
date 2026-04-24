#!/usr/bin/env python3
"""Correct NG-slab closure test.

`sk_nonempty_of_self_map` needs S ⊆ NG with a self-map f where f(c) is a
forced neighbor of c. If S = Slab(q, v) ∩ NG, then we need every c ∈ S
to have a forced NG-neighbor c' with c'[q] = v (so c' ∈ S).

Since firing at q changes c[q] (mover must change value), c' ∈ Slab(q,v)
requires firing at p ≠ q.

So the condition is:
  ∀ c ∈ Slab(q, v) ∩ NG, ∃ forced move at p ≠ q such that
    (a) firing at p from c gives c' ∈ NG, i.e., c' is not on the cycle,
    AND (b) c'[q] = v (automatic since p ≠ q and firing only changes c[p]).

So (b) is free. We just need ∀ c ∈ Slab ∩ NG, ∃ p ≠ q: det(ctx_p(c)) exists
AND applying it gives a config ∉ cycle.

Test:
  N1: For each (q, v), does every c ∈ Slab(q,v) ∩ NG have such a forced
      non-q NG-neighbor?
  N2: If yes for some (q, v), we have a direct self-map proof.
  N3: How does this scale with n?

NB: we also weaken to "c' ∈ NG" instead of "c' ∈ Slab ∩ NG" — they're
equivalent since firing at p ≠ q preserves c[q].
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


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    # Precompute forced NG-neighbors, indexed by firing position
    # fn_ng[c] = list of (p, c') where firing at p from c is determined
    #            AND c' is in VC_NG
    fn_ng = {}
    for c in VC_NG:
        nbrs = []
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                v = move_entries[ctx]
                nc = list(c); nc[p] = v; nc = tuple(nc)
                if nc in VC_NG:
                    nbrs.append((p, nc))
        fn_ng[c] = nbrs

    # For each (q, v), test N1
    works_count = 0
    works_examples = []
    T_nonempty = 0
    smallest_working = None
    for q in range(n):
        for v in V[q]:
            T = {c for c in VC_NG if c[q] == v}
            if not T: continue
            T_nonempty += 1
            ok = True
            for c in T:
                if not any(p != q for (p, _) in fn_ng[c]):
                    ok = False
                    break
            if ok:
                works_count += 1
                works_examples.append((q, v, len(T)))
                if smallest_working is None or len(T) < smallest_working[2]:
                    smallest_working = (q, v, len(T))

    # Fallback: is there ANY single config c ∈ VC_NG with a forced NG-neighbor?
    any_forced_edge = any(fn_ng[c] for c in VC_NG)

    return {
        'n': n, 'ms': ms, 'L': L,
        'VC_NG_size': len(VC_NG),
        'T_nonempty_count': T_nonempty,
        'works_count': works_count,
        'any_works': works_count > 0,
        'any_forced_edge': any_forced_edge,
        'smallest_working_size': smallest_working[2] if smallest_working else None,
    }


def main():
    print("=" * 72)
    print("NG-slab closure probe: ∃ (q,v) with Slab(q,v)∩NG self-closed via non-q?")
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
        any_w = sum(1 for r in recs if r['any_works'])
        works_dist = Counter(r['works_count'] for r in recs)
        any_fe = sum(1 for r in recs if r['any_forced_edge'])
        print(f"\n  n={n}  records={len(recs)}")
        print(f"    ANY (q,v) self-closed:   {any_w}/{len(recs)} ({100*any_w/len(recs):.1f}%)")
        print(f"    ANY forced NG-edge:      {any_fe}/{len(recs)} ({100*any_fe/len(recs):.1f}%)")
        print(f"    # working (q,v) dist (top 5): {dict(works_dist.most_common(5))}")
        if any_w < len(recs):
            print(f"    FAILING examples (first 3):")
            for r in recs:
                if not r['any_works']:
                    print(f"      ms={r['ms']} L={r['L']} VC_NG={r['VC_NG_size']}")
                    # only print first 3
                    pass
            failing = [r for r in recs if not r['any_works']]
            for r in failing[:3]:
                print(f"      ms={r['ms']} L={r['L']} VC_NG={r['VC_NG_size']}")


if __name__ == "__main__":
    main()
