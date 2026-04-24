#!/usr/bin/env python3
"""Universal binary slice balance test.

Claim (B'): for any cycle and any p* with ms[p*]=2 (hence |V[p*]|=2),
  min_v |SK ∩ {c[p*]=v}| >= 2^(n-2)

Combined with (E'): every sub-threshold ms has a binary proc, this would
give |SK| >= 2^(n-1) = Lemma C.

This probe:
  - For each cycle (L >= 2n+2), for each binary proc p (ms[p]=2):
    compute slice_0, slice_1, record min.
  - Stratify by fc[p] and record %  meeting the bound.
  - Capture any counterexamples.
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
    fc = Counter(movers)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    SK = compute_sk(VC_NG, move_entries, n)
    if not SK: return None

    # Binary procs (ms[p]=2) — |V[p]|=2 guaranteed
    bin_ps = [p for p in range(n) if ms[p] == 2]
    if not bin_ps: return None

    bound = 2 ** (n - 2)
    out = {'ms': ms, 'n': n, 'L': L, 'SK_size': len(SK),
           'bin_ps': bin_ps, 'fc': dict(fc), 'per_p': []}
    for p in bin_ps:
        v0, v1 = sorted(V[p])
        slice_0 = sum(1 for c in SK if c[p] == v0)
        slice_1 = sum(1 for c in SK if c[p] == v1)
        out['per_p'].append({
            'p': p, 'fc_p': fc[p], 'V_p_size': len(V[p]),
            'slice_0': slice_0, 'slice_1': slice_1,
            'min_slice': min(slice_0, slice_1),
            'ok': min(slice_0, slice_1) >= bound,
        })
    return out


def main():
    plan = [
        (5, 1, 50, 10.0, 22),
        (6, 3, 15, 15.0, 22),
        (7, 15, 5, 20.0, 24),
        (8, 100, 3, 20.0, 26),
    ]
    all_results = defaultdict(list)
    by_fc = defaultdict(lambda: {'total':0, 'ok':0, 'min_ratio':1.0, 'min_val':10**9, 'min_bound':0})
    ctr = defaultdict(list)
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)[::stride]
        print(f"\n=== n={n}  {len(multisets)} multisets  L_max={L_max} ===", flush=True)
        t0 = time.time()
        bound_n = 2 ** (n - 2)
        for idx, ms in enumerate(multisets):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2*n + 2: continue
                r = measure(ms, n, cycle, movers, det)
                if r is None: continue
                all_results[n].append(r)
                for pp in r['per_p']:
                    k = (n, pp['fc_p'])
                    by_fc[k]['total'] += 1
                    by_fc[k]['min_bound'] = bound_n
                    if pp['ok']: by_fc[k]['ok'] += 1
                    if pp['min_slice'] < by_fc[k]['min_val']:
                        by_fc[k]['min_val'] = pp['min_slice']
                    by_fc[k]['min_ratio'] = min(by_fc[k]['min_ratio'], pp['min_slice']/bound_n)
                    if not pp['ok']:
                        ctr[n].append({'ms': r['ms'], 'L': r['L'], 'p': pp['p'],
                                       'fc_p': pp['fc_p'], 's0': pp['slice_0'],
                                       's1': pp['slice_1'], 'bound': bound_n})
            if (idx+1) % max(1, len(multisets)//5) == 0:
                print(f"  [{idx+1}/{len(multisets)}] {time.time()-t0:.0f}s"
                      f"  recs: {len(all_results[n])} counterex: {len(ctr[n])}", flush=True)

    print(f"\n{'='*78}\nBinary slice balance @ |V|=2\n{'='*78}")
    for n in sorted(all_results):
        bound = 2 ** (n - 2)
        print(f"\n  n={n}  bound 2^(n-2) = {bound}  records: {len(all_results[n])}"
              f"  counterexamples: {len(ctr[n])}")
        rows = [(k[1], v) for k, v in by_fc.items() if k[0] == n]
        rows.sort()
        for fc_p, v in rows:
            pct = 100*v['ok']/max(1,v['total'])
            print(f"    fc_p={fc_p:>2}  total={v['total']:>5}  ok={v['ok']:>5} ({pct:.1f}%)"
                  f"  min_slice={v['min_val']}  vs bound {bound}")
        if ctr[n]:
            print(f"  First 5 counterexamples:")
            for c in ctr[n][:5]:
                print(f"    ms={c['ms']} L={c['L']} p={c['p']} fc_p={c['fc_p']}"
                      f"  slice: {c['s0']}/{c['s1']}  bound={c['bound']}")


if __name__ == "__main__":
    main()
