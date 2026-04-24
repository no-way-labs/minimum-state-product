#!/usr/bin/env python3
"""Does every good cycle of L >= 2n+2 have some p* with fc[p*]=2?

If YES, combined with proven slice balance (min_v |SK ∩ slice_v| >= 2^(n-2)
whenever p* is fc=2 binary), we get |SK| >= 2·2^(n-2) = 2^(n-1) = Lemma C.

Note: fc[p]>=1 (since movers = all n). fc[p]=k => |V[p]|=k exactly when k<=2
(fc=1 gives |V|=2, fc=2 gives |V|=2). For fc>=3, |V| can be 2..fc.

Measure: for each cycle, record fc_vec, min fc, whether any proc has fc=2.
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


def main():
    plan = [
        (5, 1, 80, 5.0, 18),
        (6, 2, 30, 8.0, 20),
        (7, 10, 8, 8.0, 22),
        (8, 50, 3, 12.0, 24),
    ]
    counterexamples_by_n = defaultdict(list)
    summary_by_n = defaultdict(lambda: {'total':0, 'has_fc2':0, 'L_dist':Counter()})

    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)[::stride]
        print(f"\n=== n={n}  {len(multisets)} multisets  L_max={L_max} ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(multisets):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2*n + 2: continue
                fc = Counter(movers)
                fc_vec = tuple(fc[p] for p in range(n))
                has_fc2 = any(fc[p] == 2 for p in range(n))
                summary_by_n[n]['total'] += 1
                summary_by_n[n]['L_dist'][L] += 1
                if has_fc2:
                    summary_by_n[n]['has_fc2'] += 1
                else:
                    # Check |V| per proc
                    V = [set() for _ in range(n)]
                    for c in cycle:
                        for i in range(n): V[i].add(c[i])
                    counterexamples_by_n[n].append({
                        'ms': ms, 'L': L, 'fc_vec': fc_vec,
                        'V_sizes': tuple(len(V[p]) for p in range(n)),
                        'min_fc': min(fc_vec), 'max_fc': max(fc_vec),
                    })
            if (idx+1) % max(1, len(multisets)//5) == 0:
                s = summary_by_n[n]
                print(f"  [{idx+1}/{len(multisets)}] {time.time()-t0:.0f}s"
                      f"  cycles L>=2n+2: {s['total']}  has_fc2: {s['has_fc2']}"
                      f"  counterex: {len(counterexamples_by_n[n])}", flush=True)

    print(f"\n{'='*78}\nfc=2 existence results\n{'='*78}")
    for n in sorted(summary_by_n):
        s = summary_by_n[n]
        ctr = counterexamples_by_n[n]
        pct = 100 * s['has_fc2'] / max(1, s['total'])
        print(f"\n  n={n}:  cycles L>=2n+2: {s['total']}"
              f"  has fc=2: {s['has_fc2']} ({pct:.1f}%)"
              f"  counterexamples: {len(ctr)}")
        if s['L_dist']:
            print(f"    L dist: {dict(sorted(s['L_dist'].items()))}")
        if ctr:
            print(f"    First 5 counterexamples:")
            for c in ctr[:5]:
                print(f"      ms={c['ms']} L={c['L']} fc={c['fc_vec']} V_sizes={c['V_sizes']}")


if __name__ == "__main__":
    main()
