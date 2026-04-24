#!/usr/bin/env python3
"""Two questions:

(A) Slice balance by processor CLASS: for each p in the record,
    compute min_slice / target and pass rate, grouped by
    (fc[p], |V[p]|, ms[p]). Which class of processor is the "best"
    pivot? Is fc=2 binary special, or does any fc=2 do it?

(B) Value-exhaustion: for each p, does every v ∈ V[p] appear in SK?
    i.e., is π_p(SK) = V[p]? If some v has |SK ∩ {c[p]=v}| = 0,
    then V[p] exhaustion fails and slice balance is trivially
    broken at that axis.
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

    bound = 2 ** (n - 1)
    per_proc = []
    for p in range(n):
        Vp = sorted(V[p])
        slices = {v: sum(1 for c in SK if c[p] == v) for v in Vp}
        min_slice = min(slices.values())
        target = bound / len(Vp)
        ratio = min_slice / target
        surjective = all(slices[v] > 0 for v in Vp)
        per_proc.append({
            'p': p,
            'fc': fc[p],
            'ms_p': ms[p],
            'V_size': len(Vp),
            'slices': slices,
            'min_slice': min_slice,
            'target': target,
            'ratio': ratio,
            'pass': min_slice >= target,
            'surjective': surjective,
            'class': (fc[p], len(Vp), ms[p]),
        })
    return {
        'ms': ms, 'n': n, 'L': L,
        'SK_size': len(SK),
        'per_proc': per_proc,
    }


def main():
    plan = [
        (5, 1, 8, 2.0, 16),
        (6, 5, 5, 3.0, 17),
        (7, 30, 3, 5.0, 18),
        (8, 300, 2, 10.0, 22),
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

    print(f"\n{'='*78}\nSlice by processor class\n{'='*78}")
    for n in sorted(by_n):
        recs = by_n[n]
        if not recs: continue
        print(f"\n  n={n}  records={len(recs)}")
        # Aggregate per-class stats
        class_stats = defaultdict(lambda: {'n_proc': 0, 'n_pass': 0,
                                           'n_surj': 0, 'ratios': [], 'min_ratios_per_rec': {}})
        best_class_per_rec = []
        for r in recs:
            # Which class gave the best (max) ratio for this record?
            best_p = max(r['per_proc'], key=lambda x: x['ratio'])
            best_class_per_rec.append(best_p['class'])
            for p_info in r['per_proc']:
                cls = p_info['class']
                cs = class_stats[cls]
                cs['n_proc'] += 1
                cs['n_pass'] += int(p_info['pass'])
                cs['n_surj'] += int(p_info['surjective'])
                cs['ratios'].append(p_info['ratio'])
        print(f"  --- per-class slice balance (fc, |V|, ms_p) ---")
        for cls in sorted(class_stats):
            cs = class_stats[cls]
            rs = cs['ratios']
            n_p = cs['n_proc']
            print(f"    fc={cls[0]} |V|={cls[1]} ms={cls[2]}  n={n_p:>5}  "
                  f"pass={cs['n_pass']:>5}/{n_p} ({100*cs['n_pass']/n_p:5.1f}%)  "
                  f"surj={cs['n_surj']:>5}/{n_p} ({100*cs['n_surj']/n_p:5.1f}%)  "
                  f"ratio min/avg/max: {min(rs):.3f}/{sum(rs)/n_p:.3f}/{max(rs):.3f}")
        # Which class is the BEST (argmax ratio) most often?
        best_counter = Counter(best_class_per_rec)
        print(f"  --- 'best p*' class distribution (argmax ratio) ---")
        for cls, cnt in sorted(best_counter.items(), key=lambda x: -x[1]):
            print(f"    fc={cls[0]} |V|={cls[1]} ms={cls[2]}: {cnt}/{len(recs)} ({100*cnt/len(recs):.1f}%)")

        # π_p(SK) surjectivity
        all_surj = sum(1 for r in recs
                       if all(p['surjective'] for p in r['per_proc']))
        print(f"  --- value-exhaustion: π_p(SK) = V[p] for ALL p ---")
        print(f"    records where ALL p are surjective: {all_surj}/{len(recs)} ({100*all_surj/len(recs):.1f}%)")
        # For non-surjective cases, which class?
        nonsurj_classes = Counter()
        for r in recs:
            for p_info in r['per_proc']:
                if not p_info['surjective']:
                    nonsurj_classes[p_info['class']] += 1
        if nonsurj_classes:
            print(f"    Non-surjective (p, class) counts: {dict(sorted(nonsurj_classes.items()))}")


if __name__ == "__main__":
    main()
