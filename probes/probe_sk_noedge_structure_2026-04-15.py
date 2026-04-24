#!/usr/bin/env python3
"""Structure of no-edge value-compatible configs.

These are the ONLY round-0 sinks within the closed value-compatible
subgraph. Understanding their count and structure gives the immune
core bound directly: immune_core ≥ |value-compat NG| - |peeled|.

For each cycle, compute:
1. |value-compat NG| = ∏|V_i| - L
2. |no-edge configs| = value-compat NG configs with zero det coverage
3. Which positions are "uncovered" at no-edge configs?
   (Does the no-edge property come from one specific position's
   context being missing, or from ALL positions?)
4. Are no-edge configs always "third-value" configs (containing
   a value at a 3-valued position that only appears in ≤1 cycle
   config)?

The hypothesis: no-edge configs are EXACTLY the configs that use
a "rare" value at a 3-valued position in a context that wasn't
visited by the cycle. Their count = (rare-value configs) which is
bounded by k × (product of other position ranges), where k = number
of extra fires.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time

def m_n_sharp(n):
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
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

def analyze_noedge(ms, n, cycle, movers, det):
    cycle_set = set(cycle)
    V = value_sets(cycle, n)
    fv = [0] * n
    for p in movers:
        fv[p] += 1

    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    # Value-compatible NG configs
    vc_ranges = [sorted(V[i]) for i in range(n)]
    vc_all = list(iproduct(*vc_ranges))
    vc_ng = [c for c in vc_all if c not in cycle_set]

    # No-edge configs
    no_edge = []
    for c in vc_ng:
        has_move = False
        for p in range(n):
            key = (p, c[(p-1)%n], c[p], c[(p+1)%n])
            if key in move_entries:
                has_move = True
                break
        if not has_move:
            no_edge.append(c)

    # Analyze no-edge configs: which positions have "uncovered" contexts?
    # A position p is "uncovered" at config c if (p, c[L], c[p], c[R]) not in move_entries
    # AND (p, c[L], c[p], c[R]) not in preserve entries (i.e., the triple never appears
    # in the cycle at position p).
    #
    # More useful: does the no-edge config use a "third value" at any 3-valued position?
    uses_third_value = 0
    strictly_binary = 0  # uses only the first 2 values at every position
    for c in no_edge:
        # "Strictly binary" = for every position i, c[i] is one of the 2 most common values
        # (= the values visited by fire_count=2 positions, or the first 2 at fire_count=3)
        has_third = False
        for i in range(n):
            if fv[i] >= 3 and len(V[i]) >= 3:
                primary = sorted(V[i])[:2]
                if c[i] not in primary:
                    has_third = True
                    break
        if has_third:
            uses_third_value += 1
        else:
            strictly_binary += 1

    return {
        'vc_ng': len(vc_ng),
        'no_edge': len(no_edge),
        'uses_third': uses_third_value,
        'strictly_binary_noedge': strictly_binary,
        'fv': tuple(sorted(fv, reverse=True)),
        'value_sizes': tuple(len(V[i]) for i in range(n)),
    }


def main():
    print("=" * 72, flush=True)
    print("No-edge structure: what are the value-compatible sinks?", flush=True)
    print("=" * 72, flush=True)

    plan = [
        (5, 1, 1500, 5.0, 15),
        (6, 4, 500, 3.0, 17),
    ]

    by_nL = defaultdict(list)
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n:
                    continue
                r = analyze_noedge(ms, n, cycle, movers, det)
                r['L'] = L
                by_nL[(n, L)].append(r)
            if (idx + 1) % 10 == 0 or idx == len(sampled) - 1:
                elapsed = time.time() - t0
                print(f"  [{idx+1}/{len(sampled)}]  {elapsed:.0f}s", flush=True)

    print(f"\n{'='*72}", flush=True)
    print(f"=== No-edge decomposition ===", flush=True)
    print(f"  n  L   count  avg_vcNG  avg_noedge  avg_third  avg_strictbin  "
          f"pct_third", flush=True)
    for (n, L) in sorted(by_nL.keys()):
        rs = by_nL[(n, L)]
        N = len(rs)
        avg = lambda k: sum(r[k] for r in rs) / N
        pct = 100 * avg('uses_third') / max(avg('no_edge'), 0.01)
        print(f"  {n}  {L:2d}  {N:5d}  {avg('vc_ng'):8.0f}  "
              f"{avg('no_edge'):10.1f}  {avg('uses_third'):9.1f}  "
              f"{avg('strictly_binary_noedge'):13.1f}  {pct:8.1f}%", flush=True)

    # Detailed: at L=2n and L=2n+2, show fv and value_sizes for a few examples
    print(f"\n=== Sample details ===", flush=True)
    for (n, L) in sorted(by_nL.keys()):
        if L not in (2*n, 2*n+2):
            continue
        rs = by_nL[(n, L)][:3]
        for i, r in enumerate(rs):
            print(f"  n={n} L={L} [{i}]: fv={r['fv']}  vsizes={r['value_sizes']}  "
                  f"vcNG={r['vc_ng']}  noedge={r['no_edge']}  "
                  f"third={r['uses_third']}  strictbin={r['strictly_binary_noedge']}",
                  flush=True)


if __name__ == "__main__":
    main()
