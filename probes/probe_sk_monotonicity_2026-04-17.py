#!/usr/bin/env python3
"""|SK| vs L monotonicity probe.

Hypothesis: for fixed n, min_{(ms,cycle,det) with cycle length L} |SK|
is non-decreasing in L.

If true: Lemma A (|SK| = 2^n - 2n - 2[n odd] at L=2n, ≥ 2^(n-1) for n≥5)
combined with monotonicity gives Lemma C (|SK| ≥ 2^(n-1) for all L ≥ 2n)
essentially for free.

Collect |SK| for all cycles at each (n, L) and look at min/avg/max.
"""
from itertools import product as iproduct
from collections import Counter, defaultdict
import time


def enumerate_multisets(n, max_product):
    out = []
    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product: out.append(tuple(prefix))
            return
        for m in range(2, max_product + 1):
            new_prod = prod * m
            min_remaining = 2 ** (n - i - 1)
            if new_prod * min_remaining >= max_product: break
            prefix.append(m); rec(i + 1, prefix, new_prod); prefix.pop()
    rec(0, [], 1)
    return out


def m_n_sharp(n):
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen_cycles = set(); t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
            km = (p, Lp, Sp, Rp); forced = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced is not None and forced != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]; ki = (i,Li,Si,Ri)
                    if ki in new_det and new_det[ki] != Si: ok = False; break
                    new_det[ki] = Si
                if not ok: continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path): continue
                dfs(start, nc, new_det, path + [nc], movers + [p])
    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget: break
        dfs(start, start, {}, [start], [])
    return found


def compute_sk(vcng_set, move_entries, n):
    current = set(vcng_set)
    while True:
        victims = set()
        for c in current:
            has_forced = False
            for p in range(n):
                ctx = (p, c[(p-1)%n], c[p], c[(p+1)%n])
                if ctx in move_entries:
                    nc = list(c); nc[p] = move_entries[ctx]; nc = tuple(nc)
                    if nc in current: has_forced = True; break
            if not has_forced: victims.add(c)
        if not victims: break
        current -= victims
    return current


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n): V[i].add(c[i])
    return V


def measure(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    SK = compute_sk(VC_NG, move_entries, n)
    return len(SK), L


def main():
    plan = [
        (5, 1, 30, 5.0, 16),
        (6, 3, 10, 5.0, 18),
        (7, 15, 4, 5.0, 20),
        (8, 100, 2, 10.0, 22),
    ]
    by_n = defaultdict(lambda: defaultdict(list))
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)[::stride]
        print(f"\n=== n={n}  {len(multisets)} multisets  L_max={L_max} ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(multisets):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                sk_size, L = measure(ms, n, cycle, movers, det)
                if sk_size == 0: continue  # VC==cycle case
                by_n[n][L].append(sk_size)
            if (idx+1) % max(1, len(multisets)//5) == 0:
                tot = sum(len(v) for v in by_n[n].values())
                print(f"  [{idx+1}/{len(multisets)}] {time.time()-t0:.0f}s recs={tot}", flush=True)

    print(f"\n{'='*78}\n|SK| vs L monotonicity\n{'='*78}")
    for n in sorted(by_n):
        bound = 2 ** (n - 1)
        print(f"\n  n={n}  bound 2^(n-1) = {bound}")
        prev_min = None
        monotone_ok = True
        for L in sorted(by_n[n]):
            sks = by_n[n][L]
            mn = min(sks); avg = sum(sks)/len(sks); mx = max(sks)
            star = ""
            if prev_min is not None and mn < prev_min:
                star = "  ← MIN DECREASED"
                monotone_ok = False
            below = sum(1 for s in sks if s < bound)
            print(f"    L={L:>2}  recs={len(sks):>5}  |SK| min/avg/max = {mn}/{avg:.1f}/{mx}  "
                  f"below bound: {below}{star}")
            prev_min = mn if prev_min is None else min(prev_min, mn)
        print(f"    Monotone-in-L (min never decreases): {monotone_ok}")


if __name__ == "__main__":
    main()
