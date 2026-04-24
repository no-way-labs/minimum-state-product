#!/usr/bin/env python3
"""Slab-pair structure probe.

The stepped distribution at n=7,8 [top=86,86,next=72*4] / [213,213,168*4]
strongly suggests the top-2 slabs come from a privileged pair of positions
(q1, q2). This probe:

  P1: Identify the (q, v) giving each of the top slabs.
  P2: Relate (q1, q2) to cycle movers/adjacency.
  P3: Is v at each top slab the non-cycle-majority value?
  P4: |Slab(q1,v1) ∪ Slab(q2,v2)| ≥ 2^(n-1) ?
  P5: |Slab(q1,v1) ∩ Slab(q2,v2)| — is the overlap small?
  P6: Slab(q,v) = {c ∈ SK : c[q]=v}. Does it have a clean structural description?
       In particular: is Slab(q,v) ⊆ (product of cycle value sets with c[q]=v), with
       an obvious combinatorial identity?
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


def compute_sk(vcng_set, move_entries, n):
    current = set(vcng_set)
    while True:
        victims = set()
        for c in current:
            has_forced = False
            for p in range(n):
                ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
                if ctx in move_entries:
                    v = move_entries[ctx]
                    nc = list(c); nc[p] = v; nc = tuple(nc)
                    if nc in current:
                        has_forced = True
                        break
            if not has_forced:
                victims.add(c)
        if not victims:
            break
        current -= victims
    return current


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    SK = compute_sk(VC_NG, move_entries, n)

    slab = defaultdict(set)
    for c in SK:
        for q in range(n):
            slab[(q, c[q])].add(c)
    # Sort slabs by size desc
    sorted_slabs = sorted(slab.items(), key=lambda kv: -len(kv[1]))
    top1 = sorted_slabs[0]; top2 = sorted_slabs[1] if len(sorted_slabs) > 1 else None
    (q1, v1), s1 = top1
    (q2, v2), s2 = (top2[0], top2[1]) if top2 else ((None, None), set())

    union = s1 | s2
    inter = s1 & s2

    # cycle-majority value at each position
    cycle_counts = [Counter(c[i] for c in cycle) for i in range(n)]
    v1_is_minority = (v1 != cycle_counts[q1].most_common(1)[0][0]) if q1 is not None else False
    v2_is_minority = (v2 != cycle_counts[q2].most_common(1)[0][0]) if q2 is not None else False

    # cycle-adjacency of (q1, q2): min((q2-q1) mod n, (q1-q2) mod n)
    if q1 is not None and q2 is not None:
        d = min((q2 - q1) % n, (q1 - q2) % n)
    else:
        d = None

    # same position?
    same_q = (q1 == q2)

    # union bound check
    bound = 2 ** (n - 1)
    union_ge = len(union) >= bound
    s1_ge = len(s1) >= bound
    top3_union = s1 | s2
    if len(sorted_slabs) >= 3:
        top3_union = top3_union | sorted_slabs[2][1]
    top3_ge = len(top3_union) >= bound

    # Can we find ANY 2 slabs whose union is ≥ bound?
    any_pair_ge = False
    entries = [(k, v) for k, v in slab.items()]
    # Greedy: pick top-1 and then find best complement
    best_pair_size = 0
    for i in range(min(5, len(entries))):
        k1, set1 = sorted_slabs[i]
        for j in range(len(entries)):
            if entries[j][0] == k1: continue
            u = len(set1 | entries[j][1])
            if u > best_pair_size:
                best_pair_size = u

    return {
        'n': n, 'ms': ms, 'L': L,
        'SK_size': len(SK),
        'bound': bound,
        'top1_slab_size': len(s1),
        'top2_slab_size': len(s2),
        's1_ge_bound': s1_ge,
        'q1': q1, 'q2': q2, 'v1': v1, 'v2': v2,
        'same_q': same_q,
        'pair_distance': d,
        'v1_minority': v1_is_minority,
        'v2_minority': v2_is_minority,
        'union_size': len(union),
        'inter_size': len(inter),
        'union_ge_bound': union_ge,
        'top3_union_ge_bound': top3_ge,
        'best_pair_size': best_pair_size,
        'best_pair_ge_bound': best_pair_size >= bound,
    }


def main():
    print("=" * 72)
    print("Slab-pair structure: which positions dominate, and their relations")
    print("=" * 72)
    plan = [
        (5, 3, 60, 3.0, 16),
        (6, 5, 25, 3.0, 17),
        (7, 30, 10, 4.0, 17),
        (8, 400, 4, 15.0, 20),
    ]
    all_records = []
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets  L_max={L_max} ===", flush=True)
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
            if (idx + 1) % max(1, len(sampled) // 10) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}")
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        if not recs: continue
        bound = 2 ** (n - 1)
        p1_s1_ge = sum(1 for r in recs if r['s1_ge_bound'])
        p4_union = sum(1 for r in recs if r['union_ge_bound'])
        best_pair = sum(1 for r in recs if r['best_pair_ge_bound'])
        top3 = sum(1 for r in recs if r['top3_union_ge_bound'])
        same_q = sum(1 for r in recs if r['same_q'])
        # (q1,q2) adjacency distribution
        dist_cnt = Counter(r['pair_distance'] for r in recs)
        minority_q1 = sum(1 for r in recs if r['v1_minority'])
        minority_q2 = sum(1 for r in recs if r['v2_minority'])
        # average sizes
        t1 = sum(r['top1_slab_size'] for r in recs) / len(recs)
        t2 = sum(r['top2_slab_size'] for r in recs) / len(recs)
        un = sum(r['union_size'] for r in recs) / len(recs)
        inter = sum(r['inter_size'] for r in recs) / len(recs)

        print(f"\n  n={n}  records={len(recs)}  bound={bound}")
        print(f"    top1 size avg={t1:.1f}  top2 avg={t2:.1f}  union avg={un:.1f}  inter avg={inter:.1f}")
        print(f"    [P1] top slab ≥ 2^(n-1):           {p1_s1_ge}/{len(recs)} ({100*p1_s1_ge/len(recs):.1f}%)")
        print(f"    [P4] top2 union ≥ 2^(n-1):         {p4_union}/{len(recs)} ({100*p4_union/len(recs):.1f}%)")
        print(f"    [P4'] best pair union ≥ 2^(n-1):   {best_pair}/{len(recs)} ({100*best_pair/len(recs):.1f}%)")
        print(f"    [P4''] top3 union ≥ 2^(n-1):       {top3}/{len(recs)} ({100*top3/len(recs):.1f}%)")
        print(f"    [P2] same position for top1,2:     {same_q}/{len(recs)} ({100*same_q/len(recs):.1f}%)")
        print(f"    [P2] (q1,q2) circular-distance dist: {dict(dist_cnt.most_common())}")
        print(f"    [P3] v1 is cycle-minority:         {minority_q1}/{len(recs)} ({100*minority_q1/len(recs):.1f}%)")
        print(f"    [P3] v2 is cycle-minority:         {minority_q2}/{len(recs)} ({100*minority_q2/len(recs):.1f}%)")


if __name__ == "__main__":
    main()
