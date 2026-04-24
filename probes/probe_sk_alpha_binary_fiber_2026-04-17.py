#!/usr/bin/env python3
"""Direct attack on P1-proj via fire-count + pigeon.

Setup: cycle C, fire count fc(p) ≥ 2 per position, sum ≥ 2n+2.
  → valueSet(p) has ≥ 2 values for each p.

Pick any q. Fix a "binary labeling" L_i ⊆ valueSet(i) with |L_i|=2 for each i ≠ q.
Consider the binary sub-codomain B_q = ∏_{i≠q} L_i, |B_q| = 2^(n-1).

STRONG CLAIM (if true, proves P1-proj sharp):
  For every b ∈ B_q, SK ∩ π_{drop-q}^{-1}(b) ≠ ∅.

Probe: for each (n, ms, cycle, q, binary labeling), count:
  - |B_q ∩ π_{drop-q}(SK)|: # binary configs "hit" by some SK fiber
  - Is this = 2^(n-1) (strong)?
  - If not, |B_q ∩ π_{drop-q}(SK)| / 2^(n-1) ratio

Also: for each q, try ALL choices of binary labeling (product of 2-element
choices from each valueSet(i)). Maximum over labelings is the key metric.

If max labeling gives FULL coverage at every n: P1-proj reduces to pigeonhole
on fire-count-derived valueSet sizes. Nice proof.
If max labeling gives partial coverage: P1-proj needs more than fire-count.
"""
from itertools import product as iproduct, combinations
from collections import defaultdict, Counter
import time
import math
import sys
sys.setrecursionlimit(100000)


def enumerate_cycles(ms, n, L_min, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen = set(); t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            if L < L_min: return
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen:
                seen.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp); forced = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced is not None and forced != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
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


def compute_sk(ms, n, cycle, det):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n): V[i].add(c[i])
    V_sorted = [sorted(V[i]) for i in range(n)]
    all_configs = list(iproduct(*V_sorted))
    cycle_set = set(cycle)
    non_good = [c for c in all_configs if c not in cycle_set]
    ng_set = set(non_good)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in move_entries:
                nc = list(c); nc[p] = move_entries[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append(nc)
    remaining = set(non_good)
    while True:
        sinks = {c for c in remaining if not any(t in remaining for t in adj.get(c, []))}
        if not sinks: break
        remaining -= sinks
    return remaining, V_sorted


def binary_fiber_probe(n, sk, V_sorted, bound):
    """For each q, for each binary labeling of positions ≠ q, compute:
       how many binary strings b ∈ {0,1}^(n-1) have SK ∩ π^{-1}(b) ≠ ∅?
    """
    sk_proj_by_q = {}
    for q in range(n):
        # Projection SK → drop-q codomain
        proj = set()
        for c in sk:
            proj.add(tuple(c[i] for i in range(n) if i != q))
        sk_proj_by_q[q] = proj

    # For each q, search over binary labelings of positions ≠ q
    results = []
    for q in range(n):
        proj = sk_proj_by_q[q]

        # For each position i ≠ q, list all 2-subsets of valueSet(i)
        labels_per_pos = []
        for i in range(n):
            if i == q: continue
            V_i = V_sorted[i]
            if len(V_i) < 2:
                labels_per_pos = None; break
            # All 2-subsets
            pairs = list(combinations(V_i, 2))
            labels_per_pos.append((i, pairs))
        if labels_per_pos is None: continue

        best_coverage = 0
        best_label = None
        best_total = 0

        # Enumerate labelings (cartesian product of 2-subsets per position)
        label_choices = [pairs for _, pairs in labels_per_pos]
        # May be large; cap at some sample
        total_labelings = 1
        for lc in label_choices: total_labelings *= len(lc)
        if total_labelings > 10000:
            # Sample: pick first 2-subset for each position (lex-smallest pair)
            label = tuple(pairs[0] for pairs in label_choices)
            B_q = set()
            pos_order = [i for i in range(n) if i != q]
            for bits in iproduct(*label):
                B_q.add(bits)
            covered = sum(1 for b in B_q if b in proj)
            best_coverage = covered
            best_label = label
            best_total = len(B_q)
        else:
            for label_tup in iproduct(*label_choices):
                pos_order = [i for i in range(n) if i != q]
                # Expand binary labeling to B_q = ∏ {label[i][0], label[i][1]}
                B_q = set()
                for bits in iproduct(*label_tup):
                    B_q.add(bits)
                covered = sum(1 for b in B_q if b in proj)
                if covered > best_coverage:
                    best_coverage = covered
                    best_label = label_tup
                    best_total = len(B_q)
                if best_coverage == 2**(n-1):
                    break

        results.append({
            'q': q, 'best_coverage': best_coverage, 'best_total': best_total,
            'proj_size': len(proj), 'bound': bound,
        })
    return results


def main():
    print("=" * 100)
    print("α-PROBE: binary sub-codomain coverage of drop-q projection of SK")
    print("=" * 100)

    plan = [
        (5, [(2,2,2,3,3), (2,2,2,3,4), (2,2,3,3,3)], 15, 3, 20.0),
        (6, [(2,2,2,3,3,3)], 17, 2, 30.0),
        (7, [(2,2,2,3,3,3,3)], 17, 1, 45.0),
        (8, [(2,2,2,3,3,3,3,3)], 19, 1, 60.0),
    ]

    for n, ms_list, L_max, max_cycles, tb in plan:
        bound = 2 ** (n - 1)
        print(f"\n=== n={n}  bound=2^{n-1}={bound} ===")
        for ms in ms_list:
            cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=L_max,
                                      time_budget=tb, max_cycles=max_cycles)
            for ci, (cycle, movers, det) in enumerate(cycles):
                sk, V_sorted = compute_sk(ms, n, cycle, det)
                if not sk: continue
                results = binary_fiber_probe(n, sk, V_sorted, bound)
                if not results: continue
                max_cov = max(r['best_coverage'] for r in results)
                print(f"\n  ms={ms} L={len(cycle)} cycle#{ci}  |SK|={len(sk)}")
                print(f"    Best coverage over all (q, labeling):  {max_cov} / {bound}  "
                      f"({'FULL' if max_cov == bound else 'PARTIAL'})")
                for r in results:
                    flag = "★" if r['best_coverage'] == bound else " "
                    print(f"     q={r['q']} best_label_coverage={r['best_coverage']}/{bound} "
                          f"|proj|={r['proj_size']}  {flag}")


if __name__ == "__main__":
    main()
