#!/usr/bin/env python3
"""WHY is slice balance true? One comprehensive probe testing 4 hypotheses:

 A. Flip-p* bijection: does flipping p* map SK_0 ↔ SK_1 (mostly)?
 B. Canonical 2^(n-2) subset: does SK_v contain an identifiable ≥ 2^(n-2) subset?
 C. Arc decomposition: does SK_v correlate with arc_v (cycle configs with p*=v)?
 D. Hamming structure: is SK_v concentrated near the v-arc of the cycle?

For each record with a binary fc-2 p*, compute:
 (1) |SK_0|, |SK_1|
 (2) Flip bijection: |{c in SK_0 : flip_p*(c) in SK_1}|
 (3) Hamming-1 intersections: |SK_v ∩ N_1(arc_v)|, |SK_v ∩ N_1(arc_{1-v})|
 (4) Cycle-nearest-arc: for each c in SK_v, is its nearest cycle config in arc_v?
 (5) Sub-bound candidates: smallest structural subset of SK_v with |.| ≥ 2^(n-2)
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


def hdist(a, b):
    return sum(1 for x, y in zip(a, b) if x != y)


def flip_p(c, p, new_val):
    return tuple(new_val if i == p else c[i] for i in range(len(c)))


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

    # Find a binary fc-2 p*. If none, skip.
    fc2_bin = [p for p in range(n) if fc[p] == 2 and len(V[p]) == 2]
    if not fc2_bin: return None
    p_star = fc2_bin[0]
    # Actual two values at p*
    v_vals = sorted(V[p_star])
    v0, v1 = v_vals[0], v_vals[1]

    # Slice SK by p*-value
    SK_0 = {c for c in SK if c[p_star] == v0}
    SK_1 = {c for c in SK if c[p_star] == v1}

    # Arc decomposition: cycle configs with p*=v0 vs p*=v1
    arc_0 = {c for c in cycle if c[p_star] == v0}
    arc_1 = {c for c in cycle if c[p_star] == v1}

    # (A) Flip-p* bijection
    flipped_SK_0 = {flip_p(c, p_star, v1) for c in SK_0}
    flipped_SK_1 = {flip_p(c, p_star, v0) for c in SK_1}
    match_0_to_1 = len(flipped_SK_0 & SK_1)
    match_1_to_0 = len(flipped_SK_1 & SK_0)
    # Union of flipped: SK_0 ∪ flipped(SK_1) → lives at p*=0
    union_at_0 = SK_0 | flipped_SK_1
    union_at_1 = SK_1 | flipped_SK_0

    # (C,D) Hamming structure per slice
    def hamming_to_arc(c, arc):
        if not arc: return None
        return min(hdist(c, a) for a in arc)

    # For each c in SK_v, nearest cycle config (Hamming distance)
    def slice_hamming_stats(SK_v, arc_v, arc_other):
        if not SK_v: return {}
        h_self = [hamming_to_arc(c, arc_v) for c in SK_v]
        h_other = [hamming_to_arc(c, arc_other) for c in SK_v]
        return {
            'size': len(SK_v),
            'h_to_self_arc': Counter(h_self),
            'h_to_other_arc': Counter(h_other),
            'n_nearest_self': sum(1 for hs, ho in zip(h_self, h_other)
                                   if hs is not None and ho is not None and hs <= ho),
            'n_nearest_other': sum(1 for hs, ho in zip(h_self, h_other)
                                    if hs is not None and ho is not None and ho < hs),
        }

    stats_0 = slice_hamming_stats(SK_0, arc_0, arc_1)
    stats_1 = slice_hamming_stats(SK_1, arc_1, arc_0)

    # (B) Canonical sub-structures
    # N_1(arc_v) = configs differing from some a in arc_v by exactly 1 coord
    def N1(arc):
        N = set()
        for a in arc:
            for i in range(n):
                for v in sorted(V[i]):
                    if v != a[i]: N.add(flip_p(a, i, v))
        return N

    N1_arc_0 = N1(arc_0) & VC
    N1_arc_1 = N1(arc_1) & VC

    bound_half = 2 ** (n - 2)

    return {
        'ms': ms, 'n': n, 'L': L,
        'SK_size': len(SK),
        'p_star': p_star,
        '|SK_0|': len(SK_0), '|SK_1|': len(SK_1),
        'bound_half': bound_half,
        'flip_match_0_to_1': match_0_to_1,   # |{c in SK_0 : flip(c) in SK_1}|
        'flip_match_1_to_0': match_1_to_0,
        'frac_matched_0': match_0_to_1/len(SK_0) if SK_0 else 0,
        'union_at_0_size': len(union_at_0),
        'union_at_1_size': len(union_at_1),
        '|arc_0|': len(arc_0), '|arc_1|': len(arc_1),
        'stats_0': stats_0, 'stats_1': stats_1,
        '|SK_0 ∩ N1(arc_0)|': len(SK_0 & N1_arc_0),
        '|SK_0 ∩ N1(arc_1)|': len(SK_0 & N1_arc_1),
        '|SK_1 ∩ N1(arc_0)|': len(SK_1 & N1_arc_0),
        '|SK_1 ∩ N1(arc_1)|': len(SK_1 & N1_arc_1),
        '|N1(arc_0) ∩ VC|': len(N1_arc_0),
        '|N1(arc_1) ∩ VC|': len(N1_arc_1),
    }


def main():
    plan = [
        (5, 1, 10, 2.0, 16),
        (6, 5, 6, 3.0, 17),
        (7, 30, 4, 5.0, 18),
        (8, 300, 3, 12.0, 22),
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

    print(f"\n{'='*78}\nSlice mechanism results\n{'='*78}")
    for n in sorted(by_n):
        recs = by_n[n]
        if not recs: continue
        total = len(recs)
        bound = 2 ** (n - 2)

        # A: flip bijection
        avg_frac = sum(r['frac_matched_0'] for r in recs) / total
        perfect_flip = sum(1 for r in recs
                           if r['flip_match_0_to_1'] == r['|SK_0|']
                           and r['flip_match_1_to_0'] == r['|SK_1|'])
        union_0_ge_bound = sum(1 for r in recs if r['union_at_0_size'] >= bound)

        # C: arc nearness
        nearest_self_0 = sum(r['stats_0'].get('n_nearest_self', 0) for r in recs)
        nearest_total_0 = sum(r['stats_0'].get('size', 0) for r in recs)
        nearest_self_1 = sum(r['stats_1'].get('n_nearest_self', 0) for r in recs)
        nearest_total_1 = sum(r['stats_1'].get('size', 0) for r in recs)

        print(f"\n  n={n}  records={total}  bound 2^(n-2)={bound}")
        print(f"  --- (A) Flip-p* bijection ---")
        print(f"    avg frac of SK_0 that flips into SK_1:  {avg_frac:.3f}")
        print(f"    records with PERFECT flip bijection:    {perfect_flip}/{total} ({100*perfect_flip/total:.1f}%)")
        print(f"    records with |SK_0 ∪ flip(SK_1)| ≥ bound: {union_0_ge_bound}/{total} ({100*union_0_ge_bound/total:.1f}%)")

        print(f"  --- (C) Arc-nearness: nearest cycle config is in SAME arc? ---")
        if nearest_total_0:
            print(f"    SK_0: nearest in arc_0:  {nearest_self_0}/{nearest_total_0} ({100*nearest_self_0/nearest_total_0:.1f}%)")
        if nearest_total_1:
            print(f"    SK_1: nearest in arc_1:  {nearest_self_1}/{nearest_total_1} ({100*nearest_self_1/nearest_total_1:.1f}%)")

        # B: N1 structure
        sub_ge = sum(1 for r in recs if r['|SK_0 ∩ N1(arc_0)|'] >= bound)
        sub_ge_cross = sum(1 for r in recs if r['|SK_0 ∩ N1(arc_1)|'] >= bound)
        print(f"  --- (B) Canonical subset candidates ---")
        print(f"    |SK_0 ∩ N_1(arc_0)| ≥ bound:  {sub_ge}/{total} ({100*sub_ge/total:.1f}%)")
        print(f"    |SK_0 ∩ N_1(arc_1)| ≥ bound:  {sub_ge_cross}/{total} ({100*sub_ge_cross/total:.1f}%)")

        # Samples
        recs_sorted = sorted(recs, key=lambda r: min(r['|SK_0|'], r['|SK_1|']))
        print(f"  Sample (tightest 3 by min slice):")
        for r in recs_sorted[:3]:
            print(f"    ms={r['ms']} L={r['L']} p*={r['p_star']} |SK|={r['SK_size']} "
                  f"|SK_0|={r['|SK_0|']} |SK_1|={r['|SK_1|']} "
                  f"flip_match 0→1={r['flip_match_0_to_1']} 1→0={r['flip_match_1_to_0']} "
                  f"|arc_0|={r['|arc_0|']} |arc_1|={r['|arc_1|']}")


if __name__ == "__main__":
    main()
