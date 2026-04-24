#!/usr/bin/env python3
"""Per-position slab bound.

Hypothesis H1: for every good cycle C and every position p:
  fc(p) := #{contexts at p witnessed by the forced-cycle rule set} ≥ 2
  ⇒ ≥ 1 unblocked (Lp, Sp, Rp, new_val) NG-entry at position p exists in VC.

Why it matters: the slab counting lemma gives a total edge count via
slabs at EACH position. If every position contributes independently
to the count, we bypass the cascade-vs-sink dichotomy because each
slab yields its own candidate out-edge, and we can collect edges from
disjoint axes.

Tests:
  H1a: Is fc(p) ≥ 2 for every p in every record?
  H1b: Does every position have ≥ 1 unblocked entry?
  H1c: Does every position have ≥ 2^(n-3) unblocked entries (the slab count)?
  H1d: Are the slab entries at different positions generically disjoint
       (edges pointing in different coordinates)?
  H1e: For each cycle config c, how many positions p have a forced
       non-stay neighbor of c in VC-NG (i.e., a successor move)?
"""
from itertools import product as iproduct
from collections import defaultdict
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
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    # fc(p): number of distinct (Lp, Sp, Rp) triples used at position p
    #        where det[(p, Lp, Sp, Rp)] ≠ Sp (i.e., mover entries)
    move_entries = [dict() for _ in range(n)]
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[p][(Lv, Sv, Rv)] = val
    fc = [len(move_entries[p]) for p in range(n)]
    # unblocked per position = number of (Lp, Sp, Rp, new_val) NG-entries
    # that live in VC and have c = (..., Sp at p, ...) in VC-NG
    unblocked_per_pos = [0] * n
    slab_per_pos = [0] * n
    # For each forced entry at position p, an "edge" in VC-NG
    # exists iff the pre-image config (Lv, Sv, Rv, rest) is in VC.
    # Simplest bound: count entries where Sv ∈ V[p] AND Lv ∈ V[(p-1)%n]
    # AND Rv ∈ V[(p+1)%n].
    for p in range(n):
        ent_live = 0
        for (Lv, Sv, Rv), val in move_entries[p].items():
            if Lv in V[(p - 1) % n] and Sv in V[p] and Rv in V[(p + 1) % n] and val in V[p]:
                ent_live += 1
        unblocked_per_pos[p] = ent_live
        slab_per_pos[p] = 2 ** (n - 3)  # the slab-counting lower bound
    # For each cycle config c, count positions p where c has a forced
    # non-stay successor edge in VC-NG (outbound NG-edge count).
    outbound_per_config = []
    for c in cycle:
        cnt = 0
        for p in range(n):
            ctx = (c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries[p]:
                cnt += 1
        outbound_per_config.append(cnt)

    return {
        'n': n, 'ms': ms, 'L': L,
        'fc_per_pos': fc,
        'unblocked_per_pos': unblocked_per_pos,
        'slab_lower': slab_per_pos,
        'all_pos_fc_ge_2': all(f >= 2 for f in fc),
        'all_pos_unblocked_ge_1': all(u >= 1 for u in unblocked_per_pos),
        'all_pos_unblocked_ge_slab': all(unblocked_per_pos[p] >= slab_per_pos[p] for p in range(n)),
        'outbound_min': min(outbound_per_config),
        'outbound_max': max(outbound_per_config),
    }


def main():
    print("=" * 72)
    print("Per-position slab bound probe — do all positions have unblocked entries?")
    print("=" * 72)
    plan = [
        (5, 1, 200, 3.0, 14),
        (6, 8, 80, 2.0, 14),
        (7, 50, 30, 3.0, 14),
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
        if not recs:
            continue
        a1 = sum(1 for r in recs if r['all_pos_fc_ge_2'])
        a2 = sum(1 for r in recs if r['all_pos_unblocked_ge_1'])
        a3 = sum(1 for r in recs if r['all_pos_unblocked_ge_slab'])
        min_fc = min(min(r['fc_per_pos']) for r in recs)
        max_fc = max(max(r['fc_per_pos']) for r in recs)
        min_ub = min(min(r['unblocked_per_pos']) for r in recs)
        max_ub = max(max(r['unblocked_per_pos']) for r in recs)
        min_ob = min(r['outbound_min'] for r in recs)
        max_ob = max(r['outbound_max'] for r in recs)
        print(f"\n  n={n}  records={len(recs)}")
        print(f"    H1a all fc(p) ≥ 2:                    {a1}/{len(recs)} ({100*a1/len(recs):.1f}%)")
        print(f"    H1b all positions have unblocked:     {a2}/{len(recs)} ({100*a2/len(recs):.1f}%)")
        print(f"    H1c unblocked ≥ slab-count 2^(n-3):   {a3}/{len(recs)} ({100*a3/len(recs):.1f}%)")
        print(f"    fc(p) range: [{min_fc}, {max_fc}]  unblocked range: [{min_ub}, {max_ub}]")
        print(f"    outbound-per-config range: [{min_ob}, {max_ob}]")


if __name__ == "__main__":
    main()
