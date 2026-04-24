#!/usr/bin/env python3
"""Slice balance: for each coord p, split SK by p-value.
   SK_v = {c in SK : c[p] = v}
   |SK| = sum_v |SK_v|
   If min_v |SK_v| ≥ 2^(n-1) / |V_p|, then |SK| ≥ 2^(n-1).

For binary fc-2 p* (|V_p|=2), the target is min(|SK_0|, |SK_1|) ≥ 2^(n-2).
This is structurally different from 2:1 fibers — it's "both halves large."

Per record, per coord:
 - slice sizes
 - min/max slice
 - does min slice reach 2^(n-1)/|V_p|?
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
            prefix.append(m)
            rec(i + 1, prefix, new_prod); prefix.pop()
    rec(0, [], 1)
    return out


def m_n_sharp(n):
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


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
    if not SK: return None

    bound = 2 ** (n - 1)
    per_coord = []
    for p in range(n):
        vp = sorted(V[p])
        slices = {v: sum(1 for c in SK if c[p] == v) for v in vp}
        sizes = sorted(slices.values())
        target = bound / len(vp)  # (2^(n-1))/|V_p|
        per_coord.append({
            'p': p, 'fc_p': fc[p], 'Vp_size': len(vp),
            'slices': slices,
            'min_slice': sizes[0], 'max_slice': sizes[-1],
            'target_per_slice': target,
            'min_ge_target': sizes[0] >= target,
        })
    return {
        'ms': ms, 'n': n, 'L': L,
        'SK_size': len(SK),
        'V_sizes': [len(v) for v in V],
        'fc': dict(fc),
        'per_coord': per_coord,
    }


def main():
    plan = [
        (5, 1, 15, 2.0, 16),
        (6, 2, 10, 3.0, 17),
        (7, 20, 5, 5.0, 18),
        (8, 150, 4, 12.0, 22),
    ]
    by_n = {}
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)[::stride]
        print(f"\n=== n={n}  {len(multisets)} multisets ===", flush=True)
        recs = []
        t0 = time.time()
        for idx, ms in enumerate(multisets):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                if len(movers) < 2*n+2: continue
                r = measure(ms, n, cycle, movers, det)
                if r is None: continue
                recs.append(r)
            if (idx+1) % max(1, len(multisets)//5) == 0:
                print(f"  [{idx+1}/{len(multisets)}] {time.time()-t0:.0f}s recs={len(recs)}", flush=True)
        by_n[n] = recs

    print(f"\n{'='*78}\nSlice-balance results\n{'='*78}")
    for n in sorted(by_n):
        recs = by_n[n]
        if not recs: continue
        total = len(recs)
        bound = 2**(n-1)

        # ∃ p with min_slice ≥ bound/|V_p|?
        any_bal = sum(1 for r in recs if any(pc['min_ge_target'] for pc in r['per_coord']))
        # fc-2 specifically
        fc2_bal = sum(1 for r in recs if any(pc['min_ge_target']
                      for pc in r['per_coord'] if pc['fc_p'] == 2))
        # binary fc-2 specifically
        bin_fc2_bal = sum(1 for r in recs if any(pc['min_ge_target']
                          for pc in r['per_coord']
                          if pc['fc_p'] == 2 and pc['Vp_size'] == 2))
        # has binary fc-2
        has_bin_fc2 = sum(1 for r in recs if any(
            pc['fc_p'] == 2 and pc['Vp_size'] == 2 for pc in r['per_coord']))

        print(f"\n  n={n}  records={total}  bound={bound}")
        print(f"    ∃ p with min_slice ≥ {bound}/|V_p|:           {any_bal:>4}/{total} ({100*any_bal/total:.1f}%)")
        print(f"    ∃ fc-2 p with balance:                       {fc2_bal:>4}/{total} ({100*fc2_bal/total:.1f}%)")
        print(f"    ∃ binary fc-2 p with balance:                {bin_fc2_bal:>4}/{total} ({100*bin_fc2_bal/total:.1f}%)")
        print(f"    records with ≥1 binary fc-2:                 {has_bin_fc2}")

        # Worst-case over records: max-over-coords min_slice/target ratio
        ratios = []
        for r in recs:
            best = max(pc['min_slice']/max(pc['target_per_slice'], 1e-9)
                       for pc in r['per_coord'])
            ratios.append(best)
        ratios.sort()
        print(f"    best min_slice/target ratio (over coord) worst 5:  {[f'{r:.3f}' for r in ratios[:5]]}")
        print(f"    best ratio avg/max:  {sum(ratios)/len(ratios):.3f} / {ratios[-1]:.3f}")

        fail = [r for r in recs if not any(pc['min_ge_target'] for pc in r['per_coord'])]
        if fail:
            print(f"    !! {len(fail)} records have NO coord with balanced slices")
            for r in fail[:3]:
                print(f"       ms={r['ms']} L={r['L']} |SK|={r['SK_size']} V={r['V_sizes']} bound={bound}")
                for pc in r['per_coord']:
                    target = pc['target_per_slice']
                    print(f"         p={pc['p']} fc={pc['fc_p']} |V|={pc['Vp_size']} "
                          f"slices={pc['slices']} min={pc['min_slice']} target={target:.1f}")


if __name__ == "__main__":
    main()
