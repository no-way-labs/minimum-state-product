#!/usr/bin/env python3
"""Threshold probe: L = 2n+2 specifically.

This is the SHORTEST cycle length where Lemma C applies. If tight
attainment of |SK| = 2^(n-1) ever happens, it should happen here.

For each L=2n+2 record we measure:
 - |SK|
 - For each fc-2 processor p*: |π_{p*}(SK)|
 - Best (max) projection size among fc-2 processors
 - Does it hit 2·Lemma_A(n-1) exactly?  (the reduction-tight value)
"""
from itertools import product as iproduct
from collections import Counter
import time


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
            if new_prod * min_remaining >= max_product: break
            prefix.append(m)
            rec(i + 1, prefix, new_prod)
            prefix.pop()
    rec(0, [], 1)
    return out


def m_n_sharp(n):
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def lemma_a_exact(n):
    return 2**n - 2*n - (2 if n % 2 else 0)


def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen_cycles = set()
    t0 = time.time()
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
    fc = Counter(movers)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    SK = compute_sk(VC_NG, move_entries, n)
    # Per fc-2 coord projection
    fc2_procs = [p for p in range(n) if fc[p] == 2]
    proj_by_fc2 = {}
    for p in fc2_procs:
        proj = {tuple(c[:p] + c[p+1:]) for c in SK}
        proj_by_fc2[p] = len(proj)
    # All-coord projections (for comparison)
    proj_all = []
    for p in range(n):
        proj_all.append(len({tuple(c[:p] + c[p+1:]) for c in SK}))
    return {
        'ms': ms, 'n': n, 'L': L,
        'SK_size': len(SK),
        'V_sizes': [len(v) for v in V],
        'fc': dict(fc),
        'fc2_procs': fc2_procs,
        'proj_fc2_max': max(proj_by_fc2.values()) if proj_by_fc2 else 0,
        'proj_fc2_min': min(proj_by_fc2.values()) if proj_by_fc2 else 0,
        'proj_all_max': max(proj_all),
        'proj_all_min': min(proj_all),
    }


def main():
    # L = 2n+2 is the shortest Lemma C length; tighter cases should live here.
    # Dense sampling where affordable.
    plan = [
        (5, 1, 30, 3.0, 12),    # L=12 exactly: Lemma C threshold at n=5
        (6, 1, 30, 4.0, 14),    # L=14
        (7, 5, 20, 6.0, 16),    # L=16
        (8, 100, 10, 12.0, 18), # L=18
    ]
    by_n = {}
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)[::stride]
        target_L = 2 * n + 2
        print(f"\n=== n={n}  {len(multisets)} multisets  targetting L={target_L} ===", flush=True)
        recs = []
        t0 = time.time()
        for idx, ms in enumerate(multisets):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                if len(movers) != target_L: continue
                r = measure(ms, n, cycle, movers, det)
                recs.append(r)
            if (idx+1) % max(1, len(multisets)//5) == 0:
                print(f"  [{idx+1}/{len(multisets)}] {time.time()-t0:.0f}s recs={len(recs)}", flush=True)
        by_n[n] = recs

    print(f"\n{'='*78}\nResults — L=2n+2 threshold\n{'='*78}")
    for n in sorted(by_n):
        recs = by_n[n]
        if not recs:
            print(f"\n  n={n}: NO RECORDS at L={2*n+2}")
            continue
        bound = 2 ** (n - 1)
        reduction_tight = 2 * lemma_a_exact(n - 1)
        sks = sorted(r['SK_size'] for r in recs)
        slack = [s - bound for s in sks]
        tight = sum(1 for s in sks if s == bound)
        red_tight = sum(1 for s in sks if s == reduction_tight)
        viol = sum(1 for s in sks if s < bound)
        fc2_maxes = sorted(r['proj_fc2_max'] for r in recs if r['fc2_procs'])
        fc2_at_bound = sum(1 for r in recs if r['fc2_procs'] and r['proj_fc2_max'] >= bound)
        has_fc2 = sum(1 for r in recs if r['fc2_procs'])

        print(f"\n  n={n}  L=2n+2={2*n+2}  records={len(recs)}")
        print(f"    bound 2^(n-1)            = {bound}")
        print(f"    reduction-tight 2·L_A(n-1) = {reduction_tight}   (= 2·(2^{n-1} - 2·{n-1} - 2·[{n-1} odd]))")
        print(f"    |SK| min/avg/max         = {sks[0]} / {sum(sks)/len(sks):.1f} / {sks[-1]}")
        print(f"    slack min/max            = {slack[0]} / {slack[-1]}")
        print(f"    # violating (|SK|<bound)      = {viol}")
        print(f"    # tight to bound              = {tight}")
        print(f"    # at reduction-tight value    = {red_tight}")
        print(f"    records with ≥1 fc-2 p*       = {has_fc2}/{len(recs)}")
        if has_fc2:
            print(f"    best fc-2 proj min/avg/max  = {fc2_maxes[0]} / {sum(fc2_maxes)/len(fc2_maxes):.1f} / {fc2_maxes[-1]}")
            print(f"    records with fc-2 proj ≥ bound = {fc2_at_bound}/{has_fc2} ({100*fc2_at_bound/has_fc2:.1f}%)")
        # 3 tightest-|SK| records
        recs_sorted = sorted(recs, key=lambda r: r['SK_size'])
        for r in recs_sorted[:3]:
            print(f"    tight sample: ms={r['ms']} |SK|={r['SK_size']} fc={r['fc']} "
                  f"fc2_proj_max={r['proj_fc2_max']} V={r['V_sizes']}")


if __name__ == "__main__":
    main()
