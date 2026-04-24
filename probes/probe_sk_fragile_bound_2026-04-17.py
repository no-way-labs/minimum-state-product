#!/usr/bin/env python3
"""Tight bound on fragile_0 at binary fc-2 pivot p*.

Goal: find an analytical upper bound on |fragile_0|, since
|SK| ≥ 2|matched_0| + |fragile_0| + |fragile_1|
    = 2(|SK_0| - |fragile_0|) + ... hmm. Let's do it carefully:

  |SK| = |SK_0| + |SK_1|
  |SK_0| = |matched_0| + |fragile_0|
  |SK_1| = |matched_1| + |fragile_1|
  |matched_0| = |matched_1| =: M

So |SK| = 2M + |fragile_0| + |fragile_1|.
Slice balance (proved empirically): min(|SK_0|, |SK_1|) ≥ 2^(n-2),
which gives |SK| ≥ 2·2^(n-2) = 2^(n-1) directly.

But we can also go via |SK| ≥ 2M where M ≥ 2^(n-2) - max(fragile_0, fragile_1).

Test candidates for |fragile_0|:
  (A) ≤ |arc_1|   (# cycle configs with c[p*]=v1)
  (B) ≤ |arc_1| / 2  (mover/non-mover parity at p*)
  (C) ≤ #(cycle configs adjacent to non-cycle via flip_{p*})
  (D) = #(arc_1 configs c such that τ(c) ∈ VC_NG)
  (E) ≤ fc[p*] = 2? (just the two firings)
  (F) equal to # arc-1 configs c with τ(c) in SK? (reverse direction)
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
    fc2_bin = [p for p in range(n) if fc[p] == 2 and len(V[p]) == 2]
    if not fc2_bin: return None
    best_p, best_ratio = None, -1
    for p in fc2_bin:
        Vp = sorted(V[p])
        slices = {v: sum(1 for c in SK if c[p] == v) for v in Vp}
        target = bound / len(Vp)
        ratio = min(slices.values()) / target
        if ratio > best_ratio:
            best_ratio = ratio; best_p = p

    p_star = best_p
    v0, v1 = sorted(V[p_star])
    SK_0 = {c for c in SK if c[p_star] == v0}
    SK_1 = {c for c in SK if c[p_star] == v1}
    arc_0 = {c for c in cycle_set if c[p_star] == v0}
    arc_1 = {c for c in cycle_set if c[p_star] == v1}
    peeled = VC_NG - SK

    def flip(c):
        cc = list(c); cc[p_star] = v1 if c[p_star] == v0 else v0
        return tuple(cc)

    matched_0 = {c for c in SK_0 if flip(c) in SK_1}
    fragile_0 = SK_0 - matched_0
    matched_1 = {c for c in SK_1 if flip(c) in SK_0}
    fragile_1 = SK_1 - matched_1

    # For fragile_0, count by where flip(c) is
    frag_0_to_cycle = sum(1 for c in fragile_0 if flip(c) in cycle_set)
    frag_0_to_peel = sum(1 for c in fragile_0 if flip(c) in peeled)

    # Candidate bounds
    bound_A = len(arc_1)                        # (A) ≤ |arc_1|
    bound_B = len(arc_0)                        # symmetry check: ≤ |arc_0|
    # (C) # cycle configs "half-touching": cycle configs whose flip is in VC_NG (not cycle)
    bound_C = sum(1 for c in cycle_set if flip(c) in VC_NG)
    # (D) # arc_1 configs c with τ(c) in VC_NG (not cycle)
    bound_D = sum(1 for c in arc_1 if flip(c) in VC_NG)
    bound_Dprime = sum(1 for c in arc_0 if flip(c) in VC_NG)  # for fragile_1
    # (E) fc[p*] = 2 always in this class
    bound_E = fc[p_star]  # always 2 here

    # arc_0 mirror: cycle configs at c[p*]=v0 whose p*-flip IS a cycle config (arc-to-arc) vs non-cycle
    arc_0_to_arc = sum(1 for c in arc_0 if flip(c) in cycle_set)
    arc_0_to_nc = sum(1 for c in arc_0 if flip(c) in VC and flip(c) not in cycle_set)
    arc_1_to_arc = sum(1 for c in arc_1 if flip(c) in cycle_set)
    arc_1_to_nc = sum(1 for c in arc_1 if flip(c) in VC and flip(c) not in cycle_set)

    return {
        'ms': ms, 'n': n, 'L': L, 'SK_size': len(SK),
        'p_star': p_star, 'v0': v0, 'v1': v1,
        'SK_0': len(SK_0), 'SK_1': len(SK_1),
        'matched_0': len(matched_0), 'fragile_0': len(fragile_0),
        'matched_1': len(matched_1), 'fragile_1': len(fragile_1),
        'frag_0_to_cycle': frag_0_to_cycle, 'frag_0_to_peel': frag_0_to_peel,
        'arc_0': len(arc_0), 'arc_1': len(arc_1),
        'peeled_size': len(peeled),
        'bound_A': bound_A, 'bound_B': bound_B, 'bound_C': bound_C,
        'bound_D': bound_D, 'bound_Dprime': bound_Dprime,
        'arc_0_to_arc': arc_0_to_arc, 'arc_0_to_nc': arc_0_to_nc,
        'arc_1_to_arc': arc_1_to_arc, 'arc_1_to_nc': arc_1_to_nc,
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

    print(f"\n{'='*78}\nFragile bound results\n{'='*78}")
    for n in sorted(by_n):
        recs = by_n[n]
        if not recs: continue
        total = len(recs)
        print(f"\n  n={n}  records={total}")
        # Fragile size distribution
        frag0 = [r['fragile_0'] for r in recs]
        frag1 = [r['fragile_1'] for r in recs]
        print(f"  fragile_0 min/avg/max: {min(frag0)}/{sum(frag0)/total:.2f}/{max(frag0)}")
        print(f"  fragile_1 min/avg/max: {min(frag1)}/{sum(frag1)/total:.2f}/{max(frag1)}")
        # Bound hit rates
        for name, key, target_key in [
            ('A: fragile_0 ≤ |arc_1|', 'fragile_0', 'bound_A'),
            ('B: fragile_0 ≤ |arc_0|', 'fragile_0', 'bound_B'),
            ('A: fragile_1 ≤ |arc_0|', 'fragile_1', 'bound_B'),
            ('fragile_0 ≤ arc_1_to_nc (arc_1 configs with flip ∉ cycle)', 'fragile_0', 'arc_1_to_nc'),
            ('fragile_0 ≤ arc_0_to_nc', 'fragile_0', 'arc_0_to_nc'),
            ('fragile_0 ≤ bound_D (arc_1 with flip in VC_NG)', 'fragile_0', 'bound_D'),
            ('fragile_0 == frag_0_to_cycle + frag_0_to_peel', 'fragile_0', None),
        ]:
            if target_key is None:
                # Sanity: fragile = cycle_part + peel_part
                ok = sum(1 for r in recs
                         if r['fragile_0'] == r['frag_0_to_cycle'] + r['frag_0_to_peel'])
                print(f"    {name}: {ok}/{total} ({100*ok/total:.1f}%)")
                continue
            ok = sum(1 for r in recs if r[key] <= r[target_key])
            eq = sum(1 for r in recs if r[key] == r[target_key])
            # slack analysis
            slacks = [r[target_key] - r[key] for r in recs]
            print(f"    {name}: holds {ok}/{total} ({100*ok/total:.1f}%)  equal {eq}/{total}  "
                  f"slack min/avg: {min(slacks)}/{sum(slacks)/total:.2f}")
        # arc_v → cycle vs non-cycle structure
        avg_a0c = sum(r['arc_0_to_arc'] for r in recs)/total
        avg_a0n = sum(r['arc_0_to_nc'] for r in recs)/total
        avg_a1c = sum(r['arc_1_to_arc'] for r in recs)/total
        avg_a1n = sum(r['arc_1_to_nc'] for r in recs)/total
        print(f"  arc_0: {avg_a0c:.2f} flip→cycle / {avg_a0n:.2f} flip→non-cycle  (total ≈ |arc_0|)")
        print(f"  arc_1: {avg_a1c:.2f} flip→cycle / {avg_a1n:.2f} flip→non-cycle  (total ≈ |arc_1|)")
        # Relationship: frag_0_to_cycle vs arc_1_to_nc?
        eq_cyc_nc = sum(1 for r in recs if r['frag_0_to_cycle'] == r['arc_1_to_nc'])
        print(f"  frag_0_to_cycle == arc_1_to_nc: {eq_cyc_nc}/{total}")


if __name__ == "__main__":
    main()
