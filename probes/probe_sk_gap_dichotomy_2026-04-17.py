#!/usr/bin/env python3
"""Gap dichotomy probe: is |SK| ∈ {0} ∪ [2^(n-1), ∞) for all (ms, cycle)?

Previous probe found |SK| values that either equal 0 or are >> 2^(n-1),
with nothing in between. This probe stress-tests the dichotomy by:
  - Enumerating MANY cycles per ms (not just 8)
  - Scanning wider range of multisets including above-threshold
  - Reporting full distribution of |SK| values
  - Flagging any value in (0, 2^(n-1)) as a gap breaker

If the gap is real, Lemma C reformulates to a STRUCTURAL statement:
"every non-empty SK has ≥ 2^(n-1) elements" — a minimum-size-of-nontrivial-
recurrent-set theorem, independent of sub-threshold hypothesis.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time
import math


def m_n_sharp(n):
    if n == 4: return 24
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


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
    return remaining


def main():
    print("=" * 100)
    print("GAP DICHOTOMY PROBE: is |SK| ∈ {0} ∪ [2^(n-1), ∞)?")
    print("=" * 100)

    # Broad ms sweep at each n, including above-threshold. More cycles per ms.
    plan = [
        # n=5
        (5, [
            (2,2,2,2,3), (2,2,2,2,4), (2,2,2,2,5),
            (2,2,2,3,3), (2,2,2,3,4), (2,2,2,4,4),
            (2,2,3,3,3), (2,2,3,3,4), (2,3,3,3,3),
            (2,2,2,3,5), (2,2,3,4,4), (2,2,3,3,5),
            (3,3,3,3,3), (2,2,2,4,5),
        ], 18, 30, 20.0),
        # n=6
        (6, [
            (2,2,2,2,3,3), (2,2,2,3,3,3), (2,2,2,3,3,4),
            (2,2,2,3,4,4), (2,2,3,3,3,3), (2,2,3,3,3,4),
        ], 18, 20, 30.0),
        # n=7
        (7, [
            (2,2,2,3,3,3,3), (2,2,2,3,3,3,4), (2,2,3,3,3,3,3),
        ], 18, 10, 45.0),
        # n=8
        (8, [
            (2,2,2,3,3,3,3,3), (2,2,2,3,3,3,3,4),
        ], 19, 6, 60.0),
    ]

    by_n = defaultdict(list)
    gap_breakers = []

    for n, ms_list, L_max, max_cycles, tb in plan:
        Mn = m_n_sharp(n)
        bound = 2 ** (n - 1)
        print(f"\n=== n={n}  M_n={Mn}  bound 2^(n-1)={bound}  "
              f"L_max={L_max} max_cycles={max_cycles} ===")
        for ms in ms_list:
            prod = math.prod(ms)
            regime = "sub" if prod < Mn else ("at" if prod == Mn else "above")
            t_ms = time.time()
            cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=L_max,
                                      time_budget=tb, max_cycles=max_cycles)
            if not cycles:
                print(f"  ms={ms!s:32s} prod={prod:<6} {regime:<5} no cycles ({time.time()-t_ms:.1f}s)")
                continue
            sk_sizes = []
            for cycle, movers, det in cycles:
                sk = compute_sk(ms, n, cycle, det)
                sk_sizes.append(len(sk))
            by_n[n].extend([(ms, prod, regime, sz) for sz in sk_sizes])

            sizes_counter = Counter(sk_sizes)
            in_gap = [s for s in sk_sizes if 0 < s < bound]
            if in_gap:
                for cycle, movers, det in cycles:
                    sk = compute_sk(ms, n, cycle, det)
                    if 0 < len(sk) < bound:
                        gap_breakers.append((n, ms, prod, regime, len(sk), bound, cycle[:3]))

            distinct = sorted(set(sk_sizes))
            print(f"  ms={ms!s:32s} prod={prod:<6} {regime:<5} "
                  f"#cyc={len(cycles):<3} L=[{min(len(c) for c,_,_ in cycles)}..{max(len(c) for c,_,_ in cycles)}] "
                  f"|SK|∈{distinct[:6]}{'…' if len(distinct)>6 else ''} "
                  f"gap={len(in_gap)}  ({time.time()-t_ms:.1f}s)")

    # Per-n distribution summary
    print("\n" + "=" * 100)
    print("PER-n DISTRIBUTION of |SK| VALUES")
    print("=" * 100)
    for n in sorted(by_n):
        recs = by_n[n]
        sizes = [sz for _, _, _, sz in recs]
        bound = 2 ** (n - 1)
        zero_count = sum(1 for s in sizes if s == 0)
        gap_count = sum(1 for s in sizes if 0 < s < bound)
        above_count = sum(1 for s in sizes if s >= bound)
        min_nonzero = min((s for s in sizes if s > 0), default=-1)
        print(f"  n={n}  bound={bound}  total_cycles={len(sizes)}  "
              f"zero={zero_count}  gap(0,{bound})={gap_count}  "
              f"≥{bound}={above_count}  min_nonzero={min_nonzero}")
        size_set = sorted(set(sizes))
        print(f"      |SK| distinct values: {size_set[:15]}{'…' if len(size_set)>15 else ''}")

    # Gap violations
    print("\n" + "=" * 100)
    print("GAP VIOLATIONS (0 < |SK| < 2^(n-1))")
    print("=" * 100)
    if not gap_breakers:
        print("  NONE — dichotomy |SK| ∈ {0} ∪ [2^(n-1), ∞) holds across all tested (ms, cycle).")
        print("  => Lemma C reformulation as gap theorem is empirically sound.")
    else:
        for n, ms, prod, regime, sz, bound, head in gap_breakers[:20]:
            print(f"  n={n} ms={ms} prod={prod} {regime} |SK|={sz} < bound={bound} "
                  f"cycle_head={head}")
        if len(gap_breakers) > 20:
            print(f"  ... and {len(gap_breakers) - 20} more.")


if __name__ == "__main__":
    main()
