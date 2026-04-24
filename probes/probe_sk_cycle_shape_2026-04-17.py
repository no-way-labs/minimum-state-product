#!/usr/bin/env python3
"""Is |SK| = f(n, L, cycle_shape) independent of ms?

Previous finding: at fixed (n, L), |SK| and SCC sizes are identical across
different ms. This suggests |SK| depends only on the cycle's combinatorial
shape, not on the specific moduli.

Extract the mover word (sequence of moved positions in the cycle) for each
(ms, cycle), group by shape, see if |SK| depends only on shape.

Key shape data:
  - L (cycle length)
  - mover pattern (e.g., "0 1 2 3 4 0 1 2 3 4" for uniform sweep)
  - fire count per position
  - value excursion pattern at each position (sequence of values visited)

If |SK| depends only on shape (not ms), then mechanism is combinatorial-geometric,
not moduli-algebraic.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time
import math


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
            km = (p, Lp, Sp, Rp)
            forced = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced is not None and forced != new_val: continue
                new_det = dict(det); new_det[km] = new_val
                ok = True
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
    return len(remaining), V_sorted


def normalize_mover_word(movers, n):
    """Canonical form of mover word under rotation and reflection."""
    L = len(movers)
    candidates = []
    for start in range(L):
        # rotation
        rot = tuple(movers[(start + i) % L] for i in range(L))
        candidates.append(rot)
        # reversal
        rev = tuple(movers[(start - i) % L] for i in range(L))
        candidates.append(rev)
    return min(candidates)


def main():
    print("=" * 100)
    print("CYCLE SHAPE INVARIANCE: is |SK| a function of cycle shape only, not ms?")
    print("=" * 100)

    plan = [
        (5, [(2,2,2,2,3), (2,2,2,3,3), (2,2,2,3,4), (2,2,2,4,4),
             (2,2,3,3,3), (2,2,3,3,4), (2,3,3,3,3), (3,3,3,3,3),
             (2,2,2,4,5), (2,2,3,4,4)], 16, 20, 30.0),
        (6, [(2,2,2,3,3,3), (2,2,2,3,3,4), (2,2,3,3,3,3),
             (2,2,3,3,3,4), (2,2,2,3,4,4), (3,3,3,3,3,3),
             (2,2,2,4,4,4)], 17, 10, 60.0),
        (7, [(2,2,2,3,3,3,3), (2,2,2,3,3,3,4),
             (2,2,3,3,3,3,3), (2,2,2,3,3,3,5),
             (2,2,2,3,3,4,4), (2,2,2,3,4,4,4)], 17, 4, 60.0),
    ]

    # shape -> list of (ms, L, sk_size)
    by_shape = defaultdict(list)

    for n, ms_list, L_max, max_cycles, tb in plan:
        print(f"\n=== n={n} ===")
        for ms in ms_list:
            cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=L_max,
                                      time_budget=tb, max_cycles=max_cycles)
            for cycle, movers, det in cycles:
                sk_sz, _ = compute_sk(ms, n, cycle, det)
                if not sk_sz: continue
                shape = normalize_mover_word(movers, n)
                # also store value_count_per_position
                V_counts = tuple(sorted(set(c[p] for c in cycle)) for p in range(n))
                V_sz = tuple(len(v) for v in V_counts)
                fc = tuple(Counter(movers)[p] for p in range(n))
                # shape key = (n, L, mover_shape, fire_counts, V_sizes)
                key = (n, len(cycle), shape, fc, V_sz)
                by_shape[key].append((ms, sk_sz))

    # Check: does every shape key have consistent sk_sz across different ms?
    print("\n" + "=" * 100)
    print("SHAPE → |SK| INVARIANCE CHECK")
    print("=" * 100)
    inconsistent = 0
    total_shapes = 0
    for key, entries in sorted(by_shape.items(), key=lambda kv: (kv[0][0], kv[0][1], kv[0][3])):
        n, L, shape, fc, V_sz = key
        ms_set = set(ms for ms, _ in entries)
        sk_set = set(sk for _, sk in entries)
        if len(sk_set) == 1 and len(ms_set) > 1:
            total_shapes += 1
            # invariant
            pass
        elif len(ms_set) > 1:
            inconsistent += 1
            total_shapes += 1
            print(f"  n={n} L={L} fc={fc} V_sz={V_sz}")
            print(f"    ms→|SK| mapping: {entries[:10]}")
        elif len(ms_set) == 1:
            total_shapes += 1

    # Overall summary
    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)
    multi_ms_shapes = [(k, v) for k, v in by_shape.items()
                       if len({ms for ms, _ in v}) > 1]
    invariant_shapes = sum(1 for k, v in multi_ms_shapes if len({sk for _, sk in v}) == 1)
    print(f"  Shapes appearing in ≥2 ms: {len(multi_ms_shapes)}")
    print(f"  Of those, |SK| invariant across ms: {invariant_shapes}")
    print(f"  |SK| VARIES with ms (shape-inconsistent): {inconsistent}")
    # per-n summary
    print("\n  Per-n key counts:")
    by_n = defaultdict(int)
    for key in by_shape:
        by_n[key[0]] += 1
    for n in sorted(by_n):
        print(f"    n={n}: {by_n[n]} distinct shapes")


if __name__ == "__main__":
    main()
