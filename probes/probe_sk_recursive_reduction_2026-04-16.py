#!/usr/bin/env python3
"""Recursive reduction test: drop fc-2 p* coord, check if reduced cycle at n-1
is still a GoodCycle and if π_{p*}(SK_n) ⊇ SK_{n-1}(reduced).

If 100%, we have the induction mechanism:
   Lemma C(n) ← |π_{p*}(SK_n)| ≥ |SK_{n-1}(reduced)| ≥ Lemma C(n-1) = 2^(n-2)
Giving |SK_n| ≥ |π(SK_n)| ≥ 2^(n-2). But we want 2^(n-1)!

Actually the simple inclusion doesn't give the right bound. So we test:
 (A) Is the reduced sequence even a valid cycle at n-1? (distinctness,
     single-coord change, covers all n-1 coords)
 (B) If yes, compute |SK_{n-1}(reduced)| and compare to 2^(n-2)
 (C) Does π_{p*}(SK_n) ⊇ SK_{n-1}(reduced)?
"""
from itertools import product as iproduct
from collections import Counter
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


def drop_coord(cycle, p):
    """Drop coord p from each config, remove consecutive duplicates to form reduced cycle."""
    reduced = []
    for c in cycle:
        reduced.append(tuple(c[:p] + c[p+1:]))
    # Remove consecutive duplicates (cycle is circular)
    out = []
    for i, x in enumerate(reduced):
        if i == 0 or x != reduced[i-1]:
            out.append(x)
    # Check wrap: first vs last
    if len(out) > 1 and out[0] == out[-1]:
        out.pop()
    return out


def check_good_cycle(reduced, n_reduced):
    """Does `reduced` form a valid good cycle at n_reduced?
    - each step changes exactly one coord
    - each of n_reduced coords fires ≥ 1 time"""
    if len(reduced) < 2: return False, None
    movers = []
    for t in range(len(reduced)):
        c = reduced[t]; nxt = reduced[(t+1) % len(reduced)]
        diffs = [i for i in range(n_reduced) if c[i] != nxt[i]]
        if len(diffs) != 1: return False, None
        movers.append(diffs[0])
    if set(movers) != set(range(n_reduced)):
        return False, None
    return True, movers


def measure(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    fc = Counter(movers)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    SK_n = compute_sk(VC_NG, move_entries, n)
    if not SK_n: return None

    bound_n = 2 ** (n - 1)
    fc2_procs = [p for p in range(n) if fc[p] == 2]
    best = None
    results = []

    for p_star in fc2_procs:
        reduced = drop_coord(cycle, p_star)
        ok, red_movers = check_good_cycle(reduced, n - 1)
        res = {'p_star': p_star, 'reduced_L': len(reduced),
               'reduced_is_gc': ok}
        if ok:
            # Compute SK_{n-1}(reduced)
            n_red = n - 1
            V_red = value_sets(reduced, n_red)
            cyc_red = set(reduced)
            VC_red = set(iproduct(*[sorted(V_red[i]) for i in range(n_red)]))
            VC_NG_red = VC_red - cyc_red
            # Build move entries for reduced cycle
            me_red = {}
            for t in range(len(reduced)):
                c = reduced[t]; nxt = reduced[(t+1) % len(reduced)]
                diffs = [i for i in range(n_red) if c[i] != nxt[i]]
                if len(diffs) != 1: break
                pp = diffs[0]
                ctx = (pp, c[(pp-1)%n_red], c[pp], c[(pp+1)%n_red])
                me_red[ctx] = nxt[pp]
            SK_red = compute_sk(VC_NG_red, me_red, n_red)
            # Check π(SK_n) ⊇ SK_red
            proj_SK_n = {tuple(c[:p_star] + c[p_star+1:]) for c in SK_n}
            contained = SK_red.issubset(proj_SK_n)
            missing = SK_red - proj_SK_n
            res['|SK_red|'] = len(SK_red)
            res['bound_red'] = 2 ** (n_red - 1)
            res['|SK_red|_ge_bound_red'] = len(SK_red) >= 2 ** (n_red - 1)
            res['|proj(SK_n)|'] = len(proj_SK_n)
            res['contained'] = contained
            res['missing_size'] = len(missing)
        results.append(res)

    return {
        'ms': ms, 'n': n, 'L': L,
        'SK_size': len(SK_n), 'V_sizes': [len(v) for v in V],
        'fc': dict(fc),
        'fc2_procs': fc2_procs,
        'per_pstar': results,
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

    print(f"\n{'='*78}\nRecursive reduction results\n{'='*78}")
    for n in sorted(by_n):
        recs = by_n[n]
        if not recs: continue
        total = len(recs)

        # How many records have ≥1 fc-2 p* with reduced = valid good cycle?
        any_red_gc = sum(1 for r in recs if any(ps['reduced_is_gc'] for ps in r['per_pstar']))
        # How many: reduced GC AND |SK_red| ≥ bound_red
        both = sum(1 for r in recs if any(
            ps['reduced_is_gc'] and ps.get('|SK_red|_ge_bound_red', False)
            for ps in r['per_pstar']))
        # How many: reduced GC AND π(SK_n) ⊇ SK_red
        both_contained = sum(1 for r in recs if any(
            ps['reduced_is_gc'] and ps.get('contained', False)
            for ps in r['per_pstar']))
        # How many: all three (reduced GC, |SK_red| big, contained)
        all_three = sum(1 for r in recs if any(
            ps['reduced_is_gc'] and ps.get('|SK_red|_ge_bound_red', False)
            and ps.get('contained', False)
            for ps in r['per_pstar']))
        has_fc2 = sum(1 for r in recs if r['fc2_procs'])

        print(f"\n  n={n}  records={total}  has ≥1 fc-2: {has_fc2}")
        print(f"    ∃ fc-2 p* : reduced is valid GC:             {any_red_gc:>4}/{total} ({100*any_red_gc/total:.1f}%)")
        print(f"    ∃ fc-2 p* : reduced GC & |SK_red| ≥ 2^(n-2): {both:>4}/{total} ({100*both/total:.1f}%)")
        print(f"    ∃ fc-2 p* : reduced GC & π(SK_n) ⊇ SK_red:   {both_contained:>4}/{total} ({100*both_contained/total:.1f}%)")
        print(f"    ∃ fc-2 p* : ALL THREE (induction):           {all_three:>4}/{total} ({100*all_three/total:.1f}%)")

        # Failure analysis: no fc-2 p* gives reduced GC
        fail_no_gc = [r for r in recs if any(ps['reduced_is_gc'] for ps in r['per_pstar']) == False]
        if fail_no_gc:
            print(f"    !! {len(fail_no_gc)} records have NO fc-2 p* with reduced = GC")
            for r in fail_no_gc[:3]:
                print(f"       ms={r['ms']} L={r['L']} fc={r['fc']}")
                for ps in r['per_pstar']:
                    print(f"         p*={ps['p_star']} reduced_L={ps['reduced_L']} is_gc={ps['reduced_is_gc']}")

        # Failure: reduced GC exists but containment fails
        fail_contain = [r for r in recs if not any(
            ps['reduced_is_gc'] and ps.get('contained', False) for ps in r['per_pstar'])]
        if fail_contain and len(fail_contain) < len(recs):
            print(f"    !! {len(fail_contain)} records lack any p* with (reduced GC) AND containment")
            for r in fail_contain[:3]:
                print(f"       ms={r['ms']} L={r['L']} |SK_n|={r['SK_size']}")
                for ps in r['per_pstar']:
                    if ps['reduced_is_gc']:
                        print(f"         p*={ps['p_star']} reduced_L={ps['reduced_L']} |SK_red|={ps.get('|SK_red|', '?')} "
                              f"contained={ps.get('contained', '?')} missing={ps.get('missing_size', '?')}")


if __name__ == "__main__":
    main()
