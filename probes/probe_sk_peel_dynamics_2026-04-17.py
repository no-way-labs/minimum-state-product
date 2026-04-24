#!/usr/bin/env python3
"""Peel dynamics at binary fc-2 p*.

Hypothesis: The peel process is 'v0/v1-balanced' — at each peel round,
the fraction of v0 vs v1 victims is close to their fraction in the
current surviving set. If so, |SK_0|/|SK_1| ≈ |VC_NG_0|/|VC_NG_1|, and
slice balance follows from VC_NG split symmetry.

Measures (at winning binary fc-2 p*):

  (1) |VC_NG_0| vs |VC_NG_1|: is the pre-peel split balanced?
  (2) For each peel round r, victims_0(r) vs victims_1(r).
  (3) Overall peel ratio: (|VC_NG_0| - |SK_0|) / (|VC_NG_1| - |SK_1|).
      Is this close to 1?
  (4) Max disparity: max over r of |v0 fraction - v1 fraction|.
  (5) Peel across p*: how often is a victim peeled because its ONLY
      forced successor was in the OTHER half?

If peel is symmetric, then the mechanism is clean:
  |VC_NG_0| = |VC_NG_1| (initial symmetry)
  → |SK_0| = |SK_1| (approximate)
  → |SK_0|, |SK_1| ≥ |SK|/2 ≥ 2^(n-2)
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


def compute_sk_with_rounds(vcng_set, move_entries, n, p_star, v0, v1):
    """Returns (SK, list of (round, victims_v0_count, victims_v1_count, total_v0, total_v1))."""
    current = set(vcng_set)
    rounds = []
    round_num = 0
    while True:
        total_v0 = sum(1 for c in current if c[p_star] == v0)
        total_v1 = sum(1 for c in current if c[p_star] == v1)
        victims = set()
        cross_victims_v0 = 0  # victims_v0 whose only dead successor was in v1 half
        cross_victims_v1 = 0
        for c in current:
            has_forced = False
            forced_successors = []
            for p in range(n):
                ctx = (p, c[(p-1)%n], c[p], c[(p+1)%n])
                if ctx in move_entries:
                    nc = list(c); nc[p] = move_entries[ctx]; nc = tuple(nc)
                    forced_successors.append((p, nc))
                    if nc in current: has_forced = True
            if not has_forced:
                victims.add(c)
                # Did all the forced successors fall into the OTHER half?
                # (i.e., was this victim 'killed' by cross-coord peels?)
                if forced_successors:
                    other_half = v1 if c[p_star] == v0 else v0
                    all_cross = all(succ[p_star] == other_half
                                    for _, succ in forced_successors)
                    if all_cross:
                        if c[p_star] == v0: cross_victims_v0 += 1
                        else: cross_victims_v1 += 1
        if not victims: break
        v_v0 = sum(1 for c in victims if c[p_star] == v0)
        v_v1 = sum(1 for c in victims if c[p_star] == v1)
        rounds.append((round_num, v_v0, v_v1, total_v0, total_v1,
                       cross_victims_v0, cross_victims_v1))
        current -= victims
        round_num += 1
    return current, rounds


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

    fc2_bin = [p for p in range(n) if fc[p] == 2 and len(V[p]) == 2]
    if not fc2_bin: return None

    results = []
    for p_star in fc2_bin:
        v0, v1 = sorted(V[p_star])
        vcng0 = sum(1 for c in VC_NG if c[p_star] == v0)
        vcng1 = sum(1 for c in VC_NG if c[p_star] == v1)
        SK, rounds = compute_sk_with_rounds(VC_NG, move_entries, n, p_star, v0, v1)
        if not SK: continue
        SK_0 = sum(1 for c in SK if c[p_star] == v0)
        SK_1 = sum(1 for c in SK if c[p_star] == v1)
        total_peel_v0 = vcng0 - SK_0
        total_peel_v1 = vcng1 - SK_1
        # Per-round victim fraction disparity
        disparities = []
        for (r, v_v0, v_v1, t_v0, t_v1, _, _) in rounds:
            if t_v0 + t_v1 == 0: continue
            frac_v0 = v_v0 / max(1, v_v0 + v_v1)  # fraction of victims at v0
            frac_total_v0 = t_v0 / (t_v0 + t_v1)   # pre-round v0 fraction
            disparities.append(frac_v0 - frac_total_v0)
        cross_v0 = sum(r[5] for r in rounds)
        cross_v1 = sum(r[6] for r in rounds)
        results.append({
            'p_star': p_star, 'v0': v0, 'v1': v1,
            'vcng0': vcng0, 'vcng1': vcng1,
            'SK_0': SK_0, 'SK_1': SK_1,
            'peel_0': total_peel_v0, 'peel_1': total_peel_v1,
            'n_rounds': len(rounds),
            'max_disparity': max(abs(d) for d in disparities) if disparities else 0,
            'avg_abs_disparity': sum(abs(d) for d in disparities)/max(1,len(disparities)),
            'cross_v0': cross_v0, 'cross_v1': cross_v1,
            'slice_balance': min(SK_0, SK_1) >= 2**(n-2),
        })

    if not results: return None
    return {
        'ms': ms, 'n': n, 'L': L,
        'fc2_bin': fc2_bin,
        'per_p_star': results,
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

    print(f"\n{'='*78}\nPeel dynamics results\n{'='*78}")
    for n in sorted(by_n):
        recs = by_n[n]
        if not recs: continue
        total = len(recs)
        print(f"\n  n={n}  records={total}")

        # Flatten across all (rec, p_star) pairs
        pairs = [(r, p) for r in recs for p in r['per_p_star']]
        print(f"  (rec, p*) pairs: {len(pairs)}")

        # (1) VC_NG split
        vcng_ratios = [p['vcng0'] / max(1, p['vcng0'] + p['vcng1']) for _, p in pairs]
        eq_vcng = sum(1 for _, p in pairs if p['vcng0'] == p['vcng1'])
        print(f"  |VC_NG_0| = |VC_NG_1|: {eq_vcng}/{len(pairs)} ({100*eq_vcng/len(pairs):.1f}%)")
        print(f"  VC_NG_0 fraction min/avg/max: {min(vcng_ratios):.3f}/{sum(vcng_ratios)/len(pairs):.3f}/{max(vcng_ratios):.3f}")

        # (3) Peel ratio
        peel_ratios = []
        for _, p in pairs:
            if p['peel_1'] == 0:
                peel_ratios.append(float('inf') if p['peel_0'] > 0 else 1.0)
            else:
                peel_ratios.append(p['peel_0'] / p['peel_1'])
        finite = [r for r in peel_ratios if r != float('inf')]
        print(f"  peel_0/peel_1 min/avg/max (finite): {min(finite):.3f}/{sum(finite)/len(finite):.3f}/{max(finite):.3f}")
        eq_peel = sum(1 for _, p in pairs if p['peel_0'] == p['peel_1'])
        print(f"  peel_0 = peel_1: {eq_peel}/{len(pairs)} ({100*eq_peel/len(pairs):.1f}%)")

        # (4) Max disparity per round
        max_disps = [p['max_disparity'] for _, p in pairs]
        avg_disps = [p['avg_abs_disparity'] for _, p in pairs]
        print(f"  max |disparity per round| min/avg/max: {min(max_disps):.3f}/{sum(max_disps)/len(pairs):.3f}/{max(max_disps):.3f}")
        print(f"  avg |disparity per round| min/avg/max: {min(avg_disps):.3f}/{sum(avg_disps)/len(pairs):.3f}/{max(avg_disps):.3f}")

        # (5) Cross-peel: victims killed by cross-half forces
        cross_v0 = [p['cross_v0'] for _, p in pairs]
        cross_v1 = [p['cross_v1'] for _, p in pairs]
        print(f"  cross_v0 (v0 victims with all forced→v1) avg: {sum(cross_v0)/len(pairs):.2f}")
        print(f"  cross_v1 (v1 victims with all forced→v0) avg: {sum(cross_v1)/len(pairs):.2f}")

        # Slice balance confirm
        sb = sum(1 for _, p in pairs if p['slice_balance'])
        print(f"  slice_balance min(|SK_0|,|SK_1|) ≥ 2^(n-2):  {sb}/{len(pairs)} ({100*sb/len(pairs):.1f}%)")


if __name__ == "__main__":
    main()
