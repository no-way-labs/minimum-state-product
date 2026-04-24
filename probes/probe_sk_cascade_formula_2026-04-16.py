#!/usr/bin/env python3
"""Cascade bound formula probe.

R1 says round-0 sinks are ≤ afford = |VC-NG| - 2^(n-1). Gap to close:
cascade (subsequent peel rounds) must not eat the remaining slack.

Test candidate analytical bounds on cascade size:
  B1: cascade ≤ uncov                    (each uncov can "kill" ≤1 covered)
  B2: cascade ≤ L                        (cycle length as upper bound)
  B3: cascade ≤ L - 2n                   (extra-fire slack)
  B4: cascade = 0                        (immune = covered)
  B5: cascade ≤ n · peeling_depth
  B6: cascade ≤ |VC-NG| - 2^(n-1) (i.e. R1's total budget minus uncov)

For each (ms, cycle):
  - compute round-by-round peeling trace: sinks per round
  - total peeled, max round, uncov=round-0 sinks, cascade=peeled-uncov
  - |SK| = |VC-NG| - peeled (immune)

Report fraction of records where each Bi holds + distribution
statistics. Find the worst-case cascade record to inspect.
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


def analyze_peel(ms, n, cycle, movers, det):
    L = len(movers)
    cycle_set = set(cycle)
    V = value_sets(cycle, n)

    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    vc_ranges = [sorted(V[i]) for i in range(n)]
    vc_all = set(iproduct(*vc_ranges))
    vc_ng = vc_all - cycle_set

    out_edges = defaultdict(set)
    for c in vc_ng:
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in move_entries:
                nc = list(c)
                nc[p] = move_entries[key]
                nc = tuple(nc)
                if nc in vc_ng:
                    out_edges[c].add(nc)

    # Peel round-by-round
    remaining = set(vc_ng)
    round_sinks = []   # |sinks| removed at each round
    while True:
        sinks = set()
        for c in remaining:
            if not any(tgt in remaining for tgt in out_edges[c]):
                sinks.add(c)
        if not sinks:
            break
        round_sinks.append(len(sinks))
        remaining -= sinks

    uncov = round_sinks[0] if round_sinks else 0
    cascade = sum(round_sinks[1:]) if len(round_sinks) > 1 else 0
    peel_depth = len(round_sinks)
    sk_size = len(remaining)
    target = 2 ** (n - 1)
    afford = len(vc_ng) - target
    vc_ng_sz = len(vc_ng)

    return {
        'L': L, 'n': n, 'ms': ms,
        'vc_ng': vc_ng_sz,
        'uncov': uncov,
        'cascade': cascade,
        'peel_depth': peel_depth,
        'sk_size': sk_size,
        'target': target,
        'afford': afford,
        'round_sinks': tuple(round_sinks),
    }


def main():
    print("=" * 72)
    print("Cascade formula probe — test analytical upper bounds on cascade")
    print("=" * 72)

    plan = [
        (5, 1, 3000, 6.0, 18),
        (6, 2, 500, 5.0, 18),
        (7, 8, 150, 4.0, 18),
        (8, 30, 50, 3.0, 18),
    ]

    all_records = []
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets (of {len(multisets)}) ===", flush=True)
        t0 = time.time()
        count = 0
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n + 2:
                    continue
                r = analyze_peel(ms, n, cycle, movers, det)
                all_records.append(r)
                count += 1
            if (idx + 1) % 30 == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    if not all_records:
        print("No records.")
        return

    print(f"\n{'='*72}")
    print(f"Cascade statistics per n  (target = 2^(n-1))")
    print(f"{'='*72}")
    by_n = defaultdict(list)
    for r in all_records:
        by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        cs = [r['cascade'] for r in recs]
        us = [r['uncov'] for r in recs]
        pd = [r['peel_depth'] for r in recs]
        Ls = [r['L'] for r in recs]
        sks = [r['sk_size'] for r in recs]
        tgt = 2 ** (n - 1)
        sk_fail = sum(1 for s in sks if s < tgt)
        print(f"\n  n={n}  records={len(recs)}  target=2^{n-1}={tgt}")
        print(f"    cascade: min={min(cs)} max={max(cs)} avg={sum(cs)/len(cs):.2f}")
        print(f"    uncov:   min={min(us)} max={max(us)} avg={sum(us)/len(us):.2f}")
        print(f"    peel_depth: min={min(pd)} max={max(pd)} avg={sum(pd)/len(pd):.2f}")
        print(f"    L:       min={min(Ls)} max={max(Ls)}")
        print(f"    SK < target:       {sk_fail} / {len(recs)}")

    # Bound tests
    print(f"\n{'='*72}")
    print(f"Bound tests")
    print(f"{'='*72}")
    bounds = {
        'B1: cascade ≤ uncov':     lambda r: r['cascade'] <= r['uncov'],
        'B2: cascade ≤ L':         lambda r: r['cascade'] <= r['L'],
        'B3: cascade ≤ L - 2n':    lambda r: r['cascade'] <= r['L'] - 2*r['n'],
        'B4: cascade = 0':         lambda r: r['cascade'] == 0,
        'B5: cascade ≤ n':         lambda r: r['cascade'] <= r['n'],
        'B6: cascade ≤ afford-uncov (from R1)': lambda r: r['cascade'] <= r['afford'] - r['uncov'],
        'B7: cascade ≤ 2(L-2n)':   lambda r: r['cascade'] <= 2*(r['L']-2*r['n']),
        'B8: uncov+cascade ≤ L':   lambda r: r['uncov']+r['cascade'] <= r['L'],
        'B9: uncov+cascade ≤ afford': lambda r: r['uncov']+r['cascade'] <= r['afford'],
    }
    for label, pred in bounds.items():
        pass_count = sum(1 for r in all_records if pred(r))
        print(f"  {label}:  {pass_count} / {len(all_records)}  ({100*pass_count/len(all_records):.1f}%)")

    # Worst-cascade cases
    print(f"\n{'='*72}")
    print(f"Worst-cascade records (top 10)")
    print(f"{'='*72}")
    worst = sorted(all_records, key=lambda r: -r['cascade'])[:10]
    for r in worst:
        slack = r['afford'] - r['uncov'] - r['cascade']
        print(f"  n={r['n']} ms={r['ms']} L={r['L']}  |VC-NG|={r['vc_ng']}  uncov={r['uncov']}  cascade={r['cascade']}  peel_depth={r['peel_depth']}  |SK|={r['sk_size']}  slack={slack}")
        print(f"    round_sinks={r['round_sinks']}")

    # Cascade vs peel_depth pattern
    print(f"\n{'='*72}")
    print(f"cascade / peel_depth correlation by n")
    print(f"{'='*72}")
    for n, recs in sorted(by_n.items()):
        by_pd = defaultdict(list)
        for r in recs:
            by_pd[r['peel_depth']].append(r['cascade'])
        print(f"\n  n={n}:")
        for pd in sorted(by_pd.keys()):
            cs = by_pd[pd]
            print(f"    peel_depth={pd}  cascade: min={min(cs)} max={max(cs)} avg={sum(cs)/len(cs):.2f}  (n_records={len(cs)})")


if __name__ == "__main__":
    main()
