#!/usr/bin/env python3
"""Fiber-size probe: is the projection π_{p*}: SK → V_{-p*} always ≥2-to-1?

If yes at some p*, then |SK| ≥ 2·|π_{p*}(SK)| — and combined with
|π_{p*}(SK)| ≥ 2^(n-2) (one level of recursion of Lemma C) we get
|SK| ≥ 2^(n-1) cleanly.

This is the structural "factor of 2" we'd need for recursive Lemma C.

Per record & per fc-2 p*:
 - min / avg / max fiber size |π^{-1}(x) ∩ SK|
 - # fibers with size ≥ 2
 - # singleton fibers (size 1)

Report:
 - records with ≥1 fc-2 p* having min_fiber ≥ 2  (the recursive goal)
 - records with ANY p* having min_fiber ≥ 2
"""
from itertools import product as iproduct
from collections import Counter, defaultdict
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

    # For each coord p: compute fiber sizes
    per_coord = []
    for p in range(n):
        fibers = defaultdict(int)
        for c in SK:
            key = c[:p] + c[p+1:]
            fibers[key] += 1
        sizes = sorted(fibers.values())
        per_coord.append({
            'p': p, 'fc_p': fc[p], 'Vp_size': len(V[p]),
            'proj_size': len(fibers),
            'min_fiber': sizes[0] if sizes else 0,
            'max_fiber': sizes[-1] if sizes else 0,
            'avg_fiber': sum(sizes) / len(sizes) if sizes else 0,
            'n_ge2': sum(1 for s in sizes if s >= 2),
            'n_singletons': sum(1 for s in sizes if s == 1),
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

    print(f"\n{'='*78}\nFiber-size results\n{'='*78}")
    for n in sorted(by_n):
        recs = by_n[n]
        if not recs: continue
        total = len(recs)

        # For each record: does ANY coord have min_fiber ≥ 2?
        any_min2 = sum(1 for r in recs if any(pc['min_fiber'] >= 2 for pc in r['per_coord']))
        # fc-2 specifically
        fc2_min2 = sum(1 for r in recs if any(
            pc['min_fiber'] >= 2 for pc in r['per_coord'] if pc['fc_p'] == 2))
        # binary-V fc-2 specifically
        bin_fc2_min2 = sum(1 for r in recs if any(
            pc['min_fiber'] >= 2 for pc in r['per_coord']
            if pc['fc_p'] == 2 and pc['Vp_size'] == 2))
        # Has binary fc-2?
        has_bin_fc2 = sum(1 for r in recs if any(
            pc['fc_p'] == 2 and pc['Vp_size'] == 2 for pc in r['per_coord']))

        print(f"\n  n={n}  records={total}")
        print(f"    ∃ p with min_fiber ≥ 2:              {any_min2:>4}/{total} ({100*any_min2/total:.1f}%)")
        print(f"    ∃ fc-2 p with min_fiber ≥ 2:         {fc2_min2:>4}/{total} ({100*fc2_min2/total:.1f}%)")
        print(f"    ∃ binary fc-2 p with min_fiber ≥ 2:  {bin_fc2_min2:>4}/{total} ({100*bin_fc2_min2/total:.1f}%)")
        print(f"    records with ≥1 binary fc-2:         {has_bin_fc2}/{total}")

        # Diagnostic: failure mode — no p achieves min_fiber ≥ 2
        fail = [r for r in recs if not any(pc['min_fiber'] >= 2 for pc in r['per_coord'])]
        if fail:
            print(f"    !! {len(fail)} records have NO coord with min_fiber ≥ 2")
            for r in fail[:3]:
                print(f"       ms={r['ms']} L={r['L']} |SK|={r['SK_size']} fc={r['fc']} V={r['V_sizes']}")
                for pc in r['per_coord']:
                    print(f"         p={pc['p']} fc={pc['fc_p']} |V|={pc['Vp_size']} "
                          f"proj={pc['proj_size']} fiber min/avg/max={pc['min_fiber']}/{pc['avg_fiber']:.1f}/{pc['max_fiber']} "
                          f"singletons={pc['n_singletons']}")

        # Aggregate: max over records of max over coords of min_fiber
        # (gives a sense of "how 2-to-1 can the best coord be")
        best_min_fibers = [max(pc['min_fiber'] for pc in r['per_coord']) for r in recs]
        dist = Counter(best_min_fibers)
        print(f"    distribution of best min_fiber over records: {dict(sorted(dist.items()))}")


if __name__ == "__main__":
    main()
