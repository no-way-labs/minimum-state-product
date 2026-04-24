#!/usr/bin/env python3
"""Slab counting → multiple unblocked entries + cycle construction.

Current slab theorem: ∃ ≥1 unblocked entry. But cycle counting says
total unblocked slots ≥ L(2^(n-3) - (n+1)), which for n=6, L≥14 gives
≥ 14·(8-7) = 14. So typically MANY unblocked edges from MANY entries.

Hypothesis: at each (ms, cycle), the set of unblocked entries covers
MULTIPLE positions. Specifically:

  (H1) ∃ ≥ 2 distinct positions each with ≥ 1 unblocked entry
  (H2) ∃ 2 positions p, q at distance ≥ 3 (disjoint neighborhoods)
       each with ≥ 1 unblocked entry
       → allows "product cycle" construction (p-move then q-move independent)
  (H3) ∃ adjacent positions p, q = (p+1)%n each with unblocked entries
       → allows 4-cycle construction via adjacent-position chain (Approach 3c)

For each cycle + det, count:
  - total unblocked entries (distinct (p, context) pairs)
  - distinct positions with unblocked entries
  - whether (H1), (H2), (H3) hold

Also test the CONSTRUCTIVE claim: given unblocked entries at p and q
with disjoint neighborhoods, does the "compose" construction give
a 4-cycle?
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


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    cycle_set = set(cycle)
    V = value_sets(cycle, n)
    move_entries = {(p, Lv, Sv, Rv): val for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    vc_ranges = [sorted(V[i]) for i in range(n)]
    vc_all = set(iproduct(*vc_ranges))
    vc_ng = vc_all - cycle_set

    # For each move entry, check if it has ≥1 unblocked instance (source + target in VC-NG)
    unblocked_entries = []    # list of (p, Lv, Sv, Rv, val, instance_count)
    unblocked_per_pos = Counter()
    for (p, Lv, Sv, Rv), val in move_entries.items():
        hits = 0
        for c in vc_ng:
            if c[(p - 1) % n] == Lv and c[p] == Sv and c[(p + 1) % n] == Rv:
                nc = list(c); nc[p] = val; nc = tuple(nc)
                if nc in vc_ng:
                    hits += 1
        if hits > 0:
            unblocked_entries.append((p, Lv, Sv, Rv, val, hits))
            unblocked_per_pos[p] += 1

    positions_with_unblocked = set(unblocked_per_pos.keys())
    num_positions = len(positions_with_unblocked)
    h1 = num_positions >= 2
    # H2: disjoint neighborhoods (distance >=3 on ring)
    h2 = False
    disjoint_pairs = []
    for p in positions_with_unblocked:
        for q in positions_with_unblocked:
            if p == q: continue
            d = min(abs(p - q), n - abs(p - q))
            if d >= 3:
                h2 = True
                disjoint_pairs.append((p, q))
    # H3: adjacent
    h3_pairs = [(p, (p + 1) % n)
                for p in positions_with_unblocked
                if ((p + 1) % n) in positions_with_unblocked]
    h3 = len(h3_pairs) > 0

    # H2 constructive: for one pair (p, q) with disjoint neighborhoods, can we construct 4-cycle?
    # 4-cycle: c0 -p-> c1 -q-> c2 -p-> c3 -q-> c0
    # Requires TWO entries at p (c0→c1 and c2→c3) and TWO entries at q (c1→c2 and c3→c0)
    # Try: find c0 such that (p entry1, q entry1, p entry2, q entry2) closes a cycle
    fc4_prod = None
    if h2:
        for (p, q) in disjoint_pairs:
            entries_p = [e for e in unblocked_entries if e[0] == p]
            entries_q = [e for e in unblocked_entries if e[0] == q]
            # For disjoint p,q: applying p-move then q-move commutes (they don't share coords)
            # So we need a,a' ∈ V_p with two p-entries that form a 2-cycle at p: toggle a↔a'
            # and similarly at q. Handoff says local 2-cycles don't exist. So this won't work.
            # But we can still try: given p-entry e1: (l,s,r)→v1 and p-entry e2: (l',s',r')→v2,
            # and q-entry: we need a config c0 where applying e1 at p gives c1, then q-entry
            # applicable at c1 gives c2, then a different p-entry applicable at c2 gives c3,
            # then q-entry applicable at c3 returns to c0.
            # This is complex. Just try computationally: for each pair of unblocked p-entries
            # and each pair of unblocked q-entries, check 4-cycle.
            for ep1 in entries_p:
                for ep2 in entries_p:
                    if ep1 == ep2: continue
                    for eq1 in entries_q:
                        for eq2 in entries_q:
                            if eq1 == eq2: continue
                            # p-entry ep1: (Lp, Sp, Rp) -> Vp
                            # c0: fix c0[p-1]=Lp1, c0[p]=Sp1, c0[p+1]=Rp1
                            # c1[p]=Vp1, rest same as c0
                            # q-entry eq1: (Lq, Sq, Rq) -> Vq on c1
                            # c1[q-1]=Lq1, c1[q]=Sq1, c1[q+1]=Rq1
                            # c2[q]=Vq1, rest same as c1
                            # etc. For p,q disjoint (|p-q|≥3), these constraints are separable.
                            # Build c0 freely in other coordinates.
                            # Check feasibility:
                            Lp1, Sp1, Rp1, Vp1 = ep1[1:5]
                            Lp2, Sp2, Rp2, Vp2 = ep2[1:5]
                            Lq1, Sq1, Rq1, Vq1 = eq1[1:5]
                            Lq2, Sq2, Rq2, Vq2 = eq2[1:5]
                            # Starting c0 has c0[p]=Sp1, after ep1 → c1[p]=Vp1
                            # c1 must satisfy eq1: c1[q]=Sq1, after eq1 → c2[q]=Vq1
                            # c2 must satisfy ep2: c2[p]=Sp2 (so Sp2 = Vp1 required for same config)
                            # Actually c2[p] = c1[p] = Vp1 (since q move doesn't touch p). So need Sp2 = Vp1.
                            if Sp2 != Vp1: continue
                            # c2[p] after ep2 → c3[p] = Vp2
                            # c3[q] = c2[q] = Vq1, then eq2 needs c3[q] = Sq2, so Sq2 = Vq1
                            if Sq2 != Vq1: continue
                            # After eq2: c4[q] = Vq2; also returning to c0 requires Vq2 = Sq1 and Vp2 = Sp1
                            if Vq2 != Sq1: continue
                            if Vp2 != Sp1: continue
                            # Neighborhood constraints: p-1, p+1, q-1, q+1 must be compatible
                            # at each config. For p,q disjoint, neighborhoods don't overlap
                            # EXCEPT if p+1=q-1 or similar. Need to check ring distance.
                            # With disjoint neighborhoods (dist≥3 on ring), all 6 indices distinct.
                            # So c0[p-1]=Lp1, c0[p+1]=Rp1, c0[q-1]=Lq1, c0[q+1]=Rq1 (all distinct).
                            # All 4 entries agree on these coordinates through the cycle:
                            #   c1 has same (p-1, p+1, q-1, q+1) as c0 except for p-1, p+1 if q-move
                            #   changes them? No: q-move only changes q.
                            # So after eq1, c2 has c1's (p-1, p+1) = c0's values. Need ep2 to apply:
                            #   c2[p-1] must = Lp2, c2[p+1] must = Rp2. So Lp2 = Lp1, Rp2 = Rp1.
                            if Lp2 != Lp1 or Rp2 != Rp1: continue
                            # c3 after ep2: c3[q-1]=c2[q-1]=c1[q-1]=c0[q-1]? Yes if p-1,p+1 ≠ q-1,q+1.
                            # For disjoint (dist≥3), indices are all distinct. So c3's (q-1,q+1) = c0's.
                            # For eq2 to apply: c3[q-1]=Lq2, c3[q+1]=Rq2. So Lq2=Lq1, Rq2=Rq1.
                            if Lq2 != Lq1 or Rq2 != Rq1: continue
                            # Feasible! Construct c0 and verify.
                            c0 = [None]*n
                            c0[(p-1)%n] = Lp1; c0[p] = Sp1; c0[(p+1)%n] = Rp1
                            c0[(q-1)%n] = Lq1; c0[q] = Sq1; c0[(q+1)%n] = Rq1
                            # Fill remaining coordinates from any VC values
                            remaining_idx = [i for i in range(n) if c0[i] is None]
                            # Just pick first available value from V[i]
                            ok = True
                            for i in remaining_idx:
                                if not V[i]: ok = False; break
                                c0[i] = sorted(V[i])[0]
                            if not ok: continue
                            c0 = tuple(c0)
                            # Build c1, c2, c3
                            c1 = list(c0); c1[p] = Vp1; c1 = tuple(c1)
                            c2 = list(c1); c2[q] = Vq1; c2 = tuple(c2)
                            c3 = list(c2); c3[p] = Vp2; c3 = tuple(c3)
                            c4 = list(c3); c4[q] = Vq2; c4 = tuple(c4)
                            if c4 == c0 and c0 not in cycle_set and c1 not in cycle_set and c2 not in cycle_set and c3 not in cycle_set:
                                fc4_prod = (c0, c1, c2, c3, p, q)
                                break
                        if fc4_prod: break
                    if fc4_prod: break
                if fc4_prod: break
            if fc4_prod: break

    return {
        'n': n, 'ms': ms, 'L': L, 'vc_ng': len(vc_ng),
        'num_unblocked_entries': len(unblocked_entries),
        'num_positions_unblocked': num_positions,
        'h1_two_positions': h1,
        'h2_disjoint_positions': h2,
        'num_disjoint_pairs': len(disjoint_pairs) // 2,
        'h3_adjacent_positions': h3,
        'num_adjacent_pairs': len(h3_pairs),
        'fc4_prod_exists': fc4_prod is not None,
        'unblocked_per_pos': dict(unblocked_per_pos),
    }


def main():
    print("=" * 72)
    print("Slab pigeonhole + constructive 4-cycle via disjoint positions")
    print("=" * 72)

    plan = [
        (5, 1, 500, 4.0, 16),
        (6, 6, 150, 3.0, 16),
        (7, 30, 60, 2.0, 16),
    ]

    all_records = []
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===", flush=True)
        t0 = time.time()
        count = 0
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n + 2:
                    continue
                r = analyze(ms, n, cycle, movers, det)
                all_records.append(r)
                count += 1
            if (idx + 1) % 10 == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}")
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        print(f"\n  n={n}  records={len(recs)}")
        h1 = sum(1 for r in recs if r['h1_two_positions'])
        h2 = sum(1 for r in recs if r['h2_disjoint_positions'])
        h3 = sum(1 for r in recs if r['h3_adjacent_positions'])
        fc4 = sum(1 for r in recs if r['fc4_prod_exists'])
        print(f"    H1 ≥2 positions unblocked:         {h1}/{len(recs)} ({100*h1/len(recs):.1f}%)")
        print(f"    H2 ≥2 disjoint positions:          {h2}/{len(recs)} ({100*h2/len(recs):.1f}%)")
        print(f"    H3 ≥2 adjacent positions:          {h3}/{len(recs)} ({100*h3/len(recs):.1f}%)")
        print(f"    FC4 product 4-cycle constructed:   {fc4}/{len(recs)} ({100*fc4/len(recs):.1f}%)")
        upe = [r['num_positions_unblocked'] for r in recs]
        print(f"    positions-unblocked: min={min(upe)} max={max(upe)} avg={sum(upe)/len(upe):.2f}")
        entries = [r['num_unblocked_entries'] for r in recs]
        print(f"    unblocked entries:   min={min(entries)} max={max(entries)} avg={sum(entries)/len(entries):.2f}")


if __name__ == "__main__":
    main()
