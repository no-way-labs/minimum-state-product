#!/usr/bin/env python3
"""Is there (q, v) such that Slab(q, v) ∩ SK is self-closed via non-q moves?

For each record and each (q, v), define
  T(q, v) := {c ∈ SK : c[q] = v}.
  self_closed(T, q) := ∀ c ∈ T, ∃ forced neighbor c' ∈ SK with firing position ≠ q.

If self_closed holds, then the map f(c) = (some such c') gives a self-map
T → T (since c' fires at p ≠ q → c'[q] = c[q] = v → c' ∈ T), and T ⊆ SK
by closed_subset_le_SK. Nonemptiness of T implies SK.Nonempty.

Tests:
  C1: For each record, is there ANY (q, v) with nonempty self-closed T?
  C2: For n ≥ 6, is this 100%?
  C3: Distribution of how many (q, v) pairs work.
  C4: Does T(q, v) = slab ∩ SK always exactly match the SK slab?
       (i.e., is every slab-SK intersection self-closed, or just some?)
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


def forced_neighbors(c, move_entries, n, within_set=None):
    """List of (p, c') pairs where firing at p gives c' ∈ within_set."""
    res = []
    for p in range(n):
        ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
        if ctx in move_entries:
            v = move_entries[ctx]
            nc = list(c); nc[p] = v; nc = tuple(nc)
            if within_set is None or nc in within_set:
                res.append((p, nc))
    return res


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    SK = compute_sk(VC_NG, move_entries, n)

    if not SK:
        return None

    # For each (q, v), define T(q,v) = {c ∈ SK : c[q] = v}
    # Check: ∀ c ∈ T, ∃ forced SK-neighbor c' with firing position ≠ q.
    works_count = 0  # number of (q,v) pairs that work
    works_examples = []
    T_nonempty = 0
    # Precompute forced SK neighbors for each c
    fn_sk = {c: forced_neighbors(c, move_entries, n, within_set=SK) for c in SK}

    for q in range(n):
        for v in V[q]:
            T = {c for c in SK if c[q] == v}
            if not T:
                continue
            T_nonempty += 1
            ok = True
            for c in T:
                if not any(p != q for (p, _) in fn_sk[c]):
                    ok = False
                    break
            if ok:
                works_count += 1
                works_examples.append((q, v, len(T)))

    # Also: for EACH c ∈ SK, list firing positions of its forced SK-neighbors
    any_works = works_count > 0

    return {
        'n': n, 'ms': ms, 'L': L,
        'SK_size': len(SK),
        'T_nonempty_count': T_nonempty,
        'works_count': works_count,
        'any_works': any_works,
        'works_examples_top3': sorted(works_examples, key=lambda t: -t[2])[:3],
    }


def main():
    print("=" * 72)
    print("Slab closure probe: ∃ (q,v) with Slab(q,v)∩SK self-closed via non-q moves?")
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
                if r is not None:
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
        nonempty_dist = Counter(r['T_nonempty_count'] for r in recs)
        print(f"\n  n={n}  records={len(recs)}")
        print(f"    ANY (q,v) works:      {any_w}/{len(recs)} ({100*any_w/len(recs):.1f}%)")
        print(f"    # (q,v) that work dist (top 5): {dict(works_dist.most_common(5))}")
        print(f"    # (q,v) with T nonempty dist (top 5): {dict(nonempty_dist.most_common(5))}")


if __name__ == "__main__":
    main()
