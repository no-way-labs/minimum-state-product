#!/usr/bin/env python3
"""Structure of binary-fiber misses in drop-q projection.

STRONG CLAIM failed by 1-2 configs at each (n, q). What are the missing
binary strings? Are they always adjacent (in some metric) to cycle
configs? Do they have a common invariant?

Plan:
  - For each (n, ms, cycle, q), find the binary labeling that maximizes
    coverage of π_{drop-q}(SK) into {0,1}^(n-1).
  - List the missing binary strings b ∈ B_q \\ π(SK).
  - For each missed b, check:
     * Is b in π_{drop-q}(C)? (cycle configs)
     * Distance from b to nearest cycle config (in drop-q space)
     * Does the drop-q fiber over b contain ANY config in VC_NG?
     * Do all configs in the fiber fail the monotonicity peel?

Also: try a SMARTER reformulation — rather than binary sub-codomain,
just verify |π_{drop-q}(SK)| ≥ 2^(n-1) DIRECTLY without the sub-codomain
restriction. Is there a clean combinatorial interpretation?
"""
from itertools import product as iproduct, combinations
from collections import defaultdict, Counter
import time, sys
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


def probe_missing(n, ms, cycle, det, bound):
    sk, V_sorted = compute_sk(ms, n, cycle, det)
    if not sk: return None

    cycle_set = set(cycle)
    rep = {}
    for q in range(n):
        proj_sk = {tuple(c[i] for i in range(n) if i != q) for c in sk}
        proj_c = {tuple(c[i] for i in range(n) if i != q) for c in cycle_set}

        # Try all binary labelings; find one with max coverage; enumerate misses
        labels_per_pos = []
        skip = False
        for i in range(n):
            if i == q: continue
            if len(V_sorted[i]) < 2: skip = True; break
            labels_per_pos.append(list(combinations(V_sorted[i], 2)))
        if skip: continue

        total = 1
        for lc in labels_per_pos: total *= len(lc)
        if total > 50000: continue

        best = None
        for label in iproduct(*labels_per_pos):
            B = list(iproduct(*label))
            covered = [b for b in B if b in proj_sk]
            missed  = [b for b in B if b not in proj_sk]
            if best is None or len(covered) > best['cov']:
                best = {'label': label, 'cov': len(covered), 'missed': missed,
                        'B_size': len(B), 'proj_c_overlap_missed':
                        [b for b in missed if b in proj_c]}
                if best['cov'] == 2**(n-1): break

        rep[q] = best

    # Direct proj sizes (unrestricted)
    proj_sizes = {q: len({tuple(c[i] for i in range(n) if i != q) for c in sk})
                  for q in range(n)}

    return {'|SK|': len(sk), 'bound': bound, 'proj_sizes': proj_sizes,
            'rep': rep, 'cycle_len': len(cycle)}


def main():
    print("=" * 100)
    print("MISSING STRUCTURE in binary-fiber coverage; direct |π(SK)| sizes")
    print("=" * 100)

    plan = [
        (5, [(2,2,2,3,3)], 14, 2, 12.0),
        (6, [(2,2,2,3,3,3)], 16, 1, 20.0),
        (7, [(2,2,2,3,3,3,3)], 17, 1, 30.0),
    ]

    for n, ms_list, L_max, max_cycles, tb in plan:
        bound = 2 ** (n - 1)
        print(f"\n=== n={n} bound={bound} ===")
        for ms in ms_list:
            cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=L_max,
                                      time_budget=tb, max_cycles=max_cycles)
            for ci, (cycle, movers, det) in enumerate(cycles):
                r = probe_missing(n, ms, cycle, det, bound)
                if r is None: continue
                print(f"\n ms={ms} L={r['cycle_len']} cycle#{ci}  |SK|={r['|SK|']}")
                print(f"   direct |π_{{drop-q}}(SK)| sizes: {r['proj_sizes']}")
                for q, best in r['rep'].items():
                    miss = best['missed']
                    c_overlap = best['proj_c_overlap_missed']
                    print(f"   q={q} cov={best['cov']}/{best['B_size']}")
                    print(f"       missed={miss}")
                    print(f"       missed ∩ π(C)={c_overlap}")


if __name__ == "__main__":
    main()
