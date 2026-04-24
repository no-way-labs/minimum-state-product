#!/usr/bin/env python3
"""Slice Tree probe: for k = 1, 2, ..., k_max binary fc-2 processors,
check if SK splits into 2^k octants each of size >= 2^(n-1-k).

If true, this is a stronger invariant than slice balance — a nested cube
structure on binary fc-2 axes.
"""
from itertools import product as iproduct, combinations
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

    # Find all binary fc-2 processors
    fc2_bin = [p for p in range(n) if fc[p] == 2 and len(V[p]) == 2]
    if not fc2_bin: return None
    bin_vals = {p: sorted(V[p]) for p in fc2_bin}

    # For each k = 1..|fc2_bin|, find BEST subset of k axes (max min-octant).
    # Stop if min-octant < 2^(n-1-k).
    results = {}  # k -> (best min-oct, target, subset, pass)
    kmax = min(len(fc2_bin), n - 2)  # bound meaningful only while 2^(n-1-k) >= 1
    for k in range(1, kmax + 1):
        target = 2 ** (n - 1 - k)
        best = -1
        best_subset = None
        best_octs = None
        for subset in combinations(fc2_bin, k):
            # Enumerate 2^k octants
            vals_list = [bin_vals[p] for p in subset]
            octs = {}
            for pattern in iproduct(*vals_list):
                cnt = sum(1 for c in SK if all(c[subset[i]] == pattern[i] for i in range(k)))
                octs[pattern] = cnt
            mn = min(octs.values())
            if mn > best:
                best = mn
                best_subset = subset
                best_octs = dict(octs)
        ok = best >= target
        results[k] = {
            'best_min_oct': best,
            'target': target,
            'subset': best_subset,
            'octs': best_octs,
            'pass': ok,
        }

    return {
        'ms': ms, 'n': n, 'L': L,
        'SK_size': len(SK),
        'n_fc2_bin': len(fc2_bin),
        'fc2_bin': fc2_bin,
        'slice_tree': results,
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

    print(f"\n{'='*78}\nSlice tree results\n{'='*78}")
    for n in sorted(by_n):
        recs = by_n[n]
        if not recs: continue
        total = len(recs)
        print(f"\n  n={n}  records={total}")
        # Group by how many binary fc-2 are available
        nb_counter = Counter(r['n_fc2_bin'] for r in recs)
        print(f"  n_binary_fc2 distribution: {dict(sorted(nb_counter.items()))}")
        # For each k, stats
        max_k = max(r['n_fc2_bin'] for r in recs)
        max_k = min(max_k, n - 2)
        for k in range(1, max_k + 1):
            target = 2 ** (n - 1 - k)
            sub_recs = [r for r in recs if k in r['slice_tree']]
            if not sub_recs: continue
            passes = sum(1 for r in sub_recs if r['slice_tree'][k]['pass'])
            best_vals = [r['slice_tree'][k]['best_min_oct'] for r in sub_recs]
            ratios = [b / target for b in best_vals]
            print(f"  k={k}  target=2^{n-1-k}={target}  records={len(sub_recs)}  "
                  f"pass={passes}/{len(sub_recs)} ({100*passes/len(sub_recs):.1f}%)  "
                  f"best_min_oct min/avg/max: {min(best_vals)}/{sum(best_vals)/len(best_vals):.1f}/{max(best_vals)}  "
                  f"ratio worst/avg: {min(ratios):.3f}/{sum(ratios)/len(ratios):.3f}")
            # Show failures
            failures = [r for r in sub_recs if not r['slice_tree'][k]['pass']]
            if failures:
                print(f"    FAILURES (first 3):")
                for r in failures[:3]:
                    sl = r['slice_tree'][k]
                    print(f"      ms={r['ms']} L={r['L']} |SK|={r['SK_size']} "
                          f"subset={sl['subset']} octs={sl['octs']} target={sl['target']}")


if __name__ == "__main__":
    main()
