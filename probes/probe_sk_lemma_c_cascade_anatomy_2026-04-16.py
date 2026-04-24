#!/usr/bin/env python3
"""Exploration 5: Cascade anatomy for SK Lemma C.

The cascade is the only remaining gap for an analytical proof. This probe
dissects it:

1. For each peeled config: what was its original out-degree? How many targets
   were cycle configs vs VC-NG configs? How many VC-NG targets survived?
2. Cascade chains: what is the max chain length (from initial sink to last
   cascade victim)?
3. The "cascade budget": how much room is there between |VC-NG| - |immune|
   and 2^(n-1)?
4. KEY TEST: does |VC-NG| - deg0 ≥ 2^(n-1) always hold? If so, and if
   all deg1+ configs with at least one edge to another deg1+ config are
   immune, the cascade bound is trivial.
5. The "self-sustaining" test: the set of configs with ≥1 edge to another
   config with ≥1 edge (transitively closed). Is this always ≥ 2^(n-1)?

Focus on multisets with some m_p ≥ 3 only (all-binary covered by Lemma A).
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


def analyze_cascade(ms, n, cycle, movers, det):
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

    # Build full edge set
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

    # Degree distribution
    deg = {c: len(out_edges[c]) for c in vc_ng}
    deg0_set = set(c for c in vc_ng if deg[c] == 0)
    deg1_set = set(c for c in vc_ng if deg[c] == 1)
    deg2plus_set = set(c for c in vc_ng if deg[c] >= 2)

    # Peel and record which round each config was peeled
    peel_round = {}
    remaining = set(vc_ng)
    rnd = 0
    while True:
        sinks = set()
        for c in remaining:
            if not any(tgt in remaining for tgt in out_edges[c]):
                sinks.add(c)
        if not sinks:
            break
        for c in sinks:
            peel_round[c] = rnd
        remaining -= sinks
        rnd += 1

    immune = remaining
    peeled = set(peel_round.keys())

    # Key test: |VC-NG| - |deg0| ≥ 2^(n-1)?
    nondeg0 = len(vc_ng) - len(deg0_set)
    target = 2 ** (n - 1)
    nondeg0_slack = nondeg0 - target

    # Cascade analysis: for each peeled non-deg0 config, what happened?
    cascade_victims = set(c for c in peeled if c not in deg0_set)
    max_peel_round = max(peel_round.values()) if peel_round else 0

    # For cascade victims: how many original targets were in immune vs peeled?
    victim_target_analysis = []
    for c in cascade_victims:
        targets = out_edges[c]
        tgt_immune = sum(1 for t in targets if t in immune)
        tgt_peeled = sum(1 for t in targets if t in peeled)
        victim_target_analysis.append({
            'deg': deg[c],
            'tgt_immune': tgt_immune,
            'tgt_peeled': tgt_peeled,
            'peel_round': peel_round[c],
        })

    # The "sufficient" test: is |configs with ≥1 edge to immune| ≥ 2^(n-1)?
    has_immune_target = set()
    for c in vc_ng:
        if any(tgt in immune for tgt in out_edges[c]):
            has_immune_target.add(c)

    return {
        'L': L,
        'vc_ng': len(vc_ng),
        'deg0': len(deg0_set),
        'deg1': len(deg1_set),
        'deg2plus': len(deg2plus_set),
        'immune': len(immune),
        'peeled': len(peeled),
        'nondeg0': nondeg0,
        'nondeg0_slack': nondeg0_slack,
        'cascade_victims': len(cascade_victims),
        'max_peel_round': max_peel_round,
        'has_immune_target': len(has_immune_target),
        'immune_reachable_slack': len(has_immune_target) - target,
    }


def main():
    print("=" * 72)
    print("Exploration 5: Cascade anatomy (mixed multisets only)")
    print("=" * 72)

    plan = [
        (5, 1, 2000, 5.0, 18),
        (6, 2, 500, 3.0, 18),
        (7, 10, 200, 3.0, 18),
    ]

    by_nL = defaultdict(list)
    all_records = []

    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        # Filter to mixed multisets (some m_i >= 3)
        mixed = [ms for ms in multisets if max(ms) >= 3]
        sampled = mixed[::stride]
        print(f"\n=== n={n}  {len(sampled)} mixed multisets (of {len(mixed)}) ===")
        t0 = time.time()
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n + 2:  # Only L >= 2n+2 (Lemma C domain)
                    continue
                r = analyze_cascade(ms, n, cycle, movers, det)
                r['n'] = n
                r['ms'] = ms
                by_nL[(n, L)].append(r)
                all_records.append(r)
            if (idx + 1) % 10 == 0 or idx == len(sampled) - 1:
                elapsed = time.time() - t0
                print(f"  [{idx + 1}/{len(sampled)}]  {elapsed:.0f}s")

    # === Key test: |VC-NG| - deg0 ≥ 2^(n-1)? ===
    print(f"\n{'='*72}")
    print("=== KEY TEST: |VC-NG| - deg0 ≥ 2^(n-1)? ===")
    print(f"  n  L   count  |VC_NG|  deg0  nondeg0  2^(n-1)  slack  "
          f"cascade_v  max_round")
    for (n, L) in sorted(by_nL.keys()):
        rs = by_nL[(n, L)]
        N = len(rs)
        avg = lambda k: sum(r[k] for r in rs) / N
        min_slack = min(r['nondeg0_slack'] for r in rs)
        max_cv = max(r['cascade_victims'] for r in rs)
        max_rd = max(r['max_peel_round'] for r in rs)
        target = 2 ** (n - 1)
        flag = " !" if min_slack < 0 else ""
        print(f"  {n}  {L:2d}  {N:5d}  {avg('vc_ng'):6.0f}  "
              f"{avg('deg0'):4.0f}  {avg('nondeg0'):7.0f}  {target:6d}  "
              f"{min_slack:+5d}  {max_cv:9d}  {max_rd:9d}{flag}")

    # === Nondeg0 >= 2^(n-1) violations ===
    nd_violations = sum(1 for r in all_records if r['nondeg0_slack'] < 0)
    print(f"\n  |VC-NG| - deg0 >= 2^(n-1): "
          f"{'HOLDS' if nd_violations == 0 else f'VIOLATED ({nd_violations})'} "
          f"({len(all_records)} records)")

    # === Immune core always equals nondeg0? (cascade = 0?) ===
    zero_cascade = sum(1 for r in all_records if r['cascade_victims'] == 0)
    print(f"\n  Cascade = 0 (immune = nondeg0): {zero_cascade} / {len(all_records)}")

    # === immune = has_immune_target? ===
    eq_count = sum(1 for r in all_records
                   if r['immune'] == r['has_immune_target'])
    print(f"  immune = |configs with ≥1 immune target|: {eq_count} / {len(all_records)}")

    # === Hardest cases by nondeg0 slack ===
    print(f"\n=== Hardest cases (lowest nondeg0 - 2^(n-1)) ===")
    sorted_records = sorted(all_records, key=lambda r: r['nondeg0_slack'])
    for r in sorted_records[:8]:
        n = r['n']
        print(f"  n={n} L={r['L']} ms={r['ms']} "
              f"vc_ng={r['vc_ng']} deg0={r['deg0']} nondeg0={r['nondeg0']} "
              f"immune={r['immune']} cascade_v={r['cascade_victims']} "
              f"nondeg0_slack={r['nondeg0_slack']:+d}")

    # === SK violations ===
    violations = sum(1 for r in all_records if r['immune'] < 2 ** (r['n'] - 1))
    print(f"\n  VC IMMUNE CORE >= 2^(n-1): "
          f"{'HOLDS' if violations == 0 else f'VIOLATED ({violations})'} "
          f"({len(all_records)} records)")


if __name__ == "__main__":
    main()
