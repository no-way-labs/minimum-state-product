#!/usr/bin/env python3
"""Flip-fragility analysis at binary fc-2 pivot p*.

For each record, pick the binary fc-2 p* that wins slice balance
(max ratio). Then for SK_0 = {c ∈ SK : c[p*] = v0}:

  - MATCHED: flip_{p*}(c) ∈ SK_1   (the "bijection-like" part)
  - FRAGILE: flip_{p*}(c) ∉ SK     (flipping destroys it)

Questions:
  1. Count / fraction fragile vs matched.
  2. Are fragile configs near arc_0 (Hamming distance to cycle
     configs with c[p*]=v0)? At Hamming dist 1, 2, ...?
  3. Is the flipped (absent) partner close to the ORIGINAL cycle?
     i.e., is flip(fragile) ⊆ N_k(cycle) for small k?
  4. Does the fragile set + its flip cover 2^(n-2)?
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


def hdist(a, b):
    return sum(1 for x, y in zip(a, b) if x != y)


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

    # Find binary fc-2 p* with best slice balance
    bound = 2 ** (n - 1)
    fc2_bin = [p for p in range(n) if fc[p] == 2 and len(V[p]) == 2]
    if not fc2_bin: return None

    best_p, best_ratio = None, -1
    for p in fc2_bin:
        Vp = sorted(V[p])
        slices = {v: sum(1 for c in SK if c[p] == v) for v in Vp}
        target = bound / len(Vp)
        ratio = min(slices.values()) / target
        if ratio > best_ratio:
            best_ratio = ratio
            best_p = p

    p_star = best_p
    v0, v1 = sorted(V[p_star])
    SK_0 = {c for c in SK if c[p_star] == v0}
    SK_1 = {c for c in SK if c[p_star] == v1}

    def flip(c):
        cc = list(c); cc[p_star] = v1 if c[p_star] == v0 else v0
        return tuple(cc)

    # Classify SK_0
    matched_0 = {c for c in SK_0 if flip(c) in SK_1}
    fragile_0 = SK_0 - matched_0
    matched_1 = {c for c in SK_1 if flip(c) in SK_0}
    fragile_1 = SK_1 - matched_1

    # For fragile configs, check what their flipped partner looks like
    # (where is flip(fragile) in the ambient space?)
    flip_frag_0_in_cycle = sum(1 for c in fragile_0 if flip(c) in cycle_set)
    flip_frag_0_in_vcng = sum(1 for c in fragile_0 if flip(c) in VC_NG)  # in peeled
    flip_frag_0_outside = sum(1 for c in fragile_0 if flip(c) not in VC)

    # Hamming distances to cycle for matched vs fragile
    cycle_list = list(cycle_set)
    def min_hdist_to_cycle(c):
        return min(hdist(c, a) for a in cycle_list)
    matched_h = [min_hdist_to_cycle(c) for c in matched_0]
    fragile_h = [min_hdist_to_cycle(c) for c in fragile_0]

    # Union size
    union_size = len(SK_0 | {flip(c) for c in SK_1})

    return {
        'ms': ms, 'n': n, 'L': L, 'SK_size': len(SK),
        'p_star': p_star, 'v0': v0, 'v1': v1,
        'SK_0_size': len(SK_0), 'SK_1_size': len(SK_1),
        'matched_0': len(matched_0), 'fragile_0': len(fragile_0),
        'matched_1': len(matched_1), 'fragile_1': len(fragile_1),
        'flip_frag_0_cycle': flip_frag_0_in_cycle,
        'flip_frag_0_peeled': flip_frag_0_in_vcng - flip_frag_0_outside,  # in VC_NG means not in cycle
        'flip_frag_0_outside': flip_frag_0_outside,
        'matched_h_dist': Counter(matched_h),
        'fragile_h_dist': Counter(fragile_h),
        'union_size': union_size,
        'bound': 2 ** (n - 2),
        'n_fc2_bin': len(fc2_bin),
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

    print(f"\n{'='*78}\nFlip fragility results\n{'='*78}")
    for n in sorted(by_n):
        recs = by_n[n]
        if not recs: continue
        total = len(recs)
        bound = 2 ** (n - 2)
        print(f"\n  n={n}  records={total}  bound 2^(n-2)={bound}")

        # Matched/fragile ratios
        matched_fracs_0 = [r['matched_0'] / max(r['SK_0_size'], 1) for r in recs]
        fragile_fracs_0 = [r['fragile_0'] / max(r['SK_0_size'], 1) for r in recs]
        print(f"  matched/|SK_0|  min/avg/max: {min(matched_fracs_0):.3f}/{sum(matched_fracs_0)/total:.3f}/{max(matched_fracs_0):.3f}")
        print(f"  fragile/|SK_0|  min/avg/max: {min(fragile_fracs_0):.3f}/{sum(fragile_fracs_0)/total:.3f}/{max(fragile_fracs_0):.3f}")

        # Where are flipped fragile partners?
        avg_frag_cyc = sum(r['flip_frag_0_cycle'] for r in recs) / total
        avg_frag_peel = sum(r['flip_frag_0_peeled'] for r in recs) / total
        avg_frag_out = sum(r['flip_frag_0_outside'] for r in recs) / total
        print(f"  flip(fragile_0) location — avg per record:")
        print(f"    in cycle:   {avg_frag_cyc:.2f}   (flipped partner IS cycle config)")
        print(f"    in peeled:  {avg_frag_peel:.2f}   (partner in VC_NG but not in SK — peeled away)")
        print(f"    outside VC: {avg_frag_out:.2f}   (partner not in ∏V[i])")

        # Hamming distributions
        print(f"  Hamming dist to cycle:")
        agg_m = Counter()
        agg_f = Counter()
        for r in recs:
            agg_m.update(r['matched_h_dist'])
            agg_f.update(r['fragile_h_dist'])
        total_m = sum(agg_m.values())
        total_f = sum(agg_f.values())
        print(f"    matched:  {dict(sorted(agg_m.items()))}  (N={total_m})")
        print(f"    fragile:  {dict(sorted(agg_f.items()))}  (N={total_f})")

        # Union ≥ 2^(n-2)
        union_ok = sum(1 for r in recs if r['union_size'] >= bound)
        print(f"  |SK_0 ∪ flip(SK_1)| ≥ 2^(n-2):  {union_ok}/{total} ({100*union_ok/total:.1f}%)")

        # Additional: ratios of matched_0 = matched_1 (since bijection)
        all_sym = sum(1 for r in recs if r['matched_0'] == r['matched_1'])
        print(f"  matched_0 == matched_1:  {all_sym}/{total}  (flip-bijection size symmetry)")


if __name__ == "__main__":
    main()
