#!/usr/bin/env python3
"""Confirm fc=2 exists at L >= 3n where pigeonhole no longer forces it.

At L >= 3n, all fc >= 3 is dimensionally possible (sum = 3n = L). We need
empirical confirmation that fc=2 STILL always exists, and ideally find
structural reason.

For n=5: L_max = 3n = 15 is right in the sweep range. Push L_max > 3n.
For n=6: L_max = 18+. For n=7: L_max = 21+.

Also record fc_vec of each cycle for structural analysis: if fc=2 exists
universally at L >> 3n, maybe there's a fixed subset of positions where
fc<=2 is forced (boundary-like).
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


def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles, L_min):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen_cycles = set(); t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            if L < L_min: return
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


def main():
    # Focus on L >= 3n where pigeonhole fails. For n=5, 3n=15.
    # Explicitly push L_max above 3n and count fc=2 existence.
    plan = [
        # (n, stride, max_cycles, tb, L_max, L_min)
        (5, 1, 50, 10.0, 22, 15),   # L>=3n=15 up to 22
        (6, 3, 15, 15.0, 24, 18),   # L>=3n=18 up to 24
        (7, 15, 5, 20.0, 26, 21),   # L>=3n=21 up to 26
    ]
    ctr_by_n = defaultdict(list)
    summary = defaultdict(lambda: {'total':0, 'has_fc2':0, 'by_L': defaultdict(lambda: {'total':0, 'has_fc2':0, 'min_fc':[]})})
    for n, stride, max_cycles, tb, L_max, L_min in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)[::stride]
        print(f"\n=== n={n}  {len(multisets)} multisets  L_min={L_min} L_max={L_max} ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(multisets):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles, L_min)
            for cycle, movers, det in cycles:
                L = len(movers)
                fc = Counter(movers)
                fc_vec = tuple(fc[p] for p in range(n))
                has_fc2 = any(fc[p] == 2 for p in range(n))
                summary[n]['total'] += 1
                summary[n]['by_L'][L]['total'] += 1
                summary[n]['by_L'][L]['min_fc'].append(min(fc_vec))
                if has_fc2:
                    summary[n]['has_fc2'] += 1
                    summary[n]['by_L'][L]['has_fc2'] += 1
                else:
                    ctr_by_n[n].append({
                        'ms': ms, 'L': L, 'fc': fc_vec,
                        'start': cycle[0], 'cycle_len': len(cycle),
                    })
            if (idx+1) % max(1, len(multisets)//5) == 0:
                s = summary[n]
                print(f"  [{idx+1}/{len(multisets)}] {time.time()-t0:.0f}s"
                      f"  total: {s['total']}  has_fc2: {s['has_fc2']}"
                      f"  counterex: {len(ctr_by_n[n])}", flush=True)

    print(f"\n{'='*78}\nfc=2 existence @ L >= 3n\n{'='*78}")
    for n in sorted(summary):
        s = summary[n]
        ctr = ctr_by_n[n]
        pct = 100 * s['has_fc2'] / max(1, s['total'])
        print(f"\n  n={n}:  total L>=3n: {s['total']}  has_fc2: {s['has_fc2']} ({pct:.1f}%)"
              f"  counterex: {len(ctr)}")
        for L in sorted(s['by_L']):
            b = s['by_L'][L]
            min_fcs = Counter(b['min_fc'])
            print(f"    L={L:>3}  total={b['total']:>4}  has_fc2={b['has_fc2']:>4}"
                  f"  min_fc dist: {dict(sorted(min_fcs.items()))}")
        if ctr:
            print(f"  First 3 counterexamples:")
            for c in ctr[:3]:
                print(f"    ms={c['ms']} L={c['L']} fc={c['fc']} start={c['start']}")


if __name__ == "__main__":
    main()
