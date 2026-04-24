#!/usr/bin/env python3
"""Verify the cone=0 hypothesis: SK = union of forced SCCs, every node recurrent.

Previous probe: at n=7,8 cone_size=0 for ALL observed (cycle, SCC) pairs.
At n=5,6 cone was small (1-2) but still mostly 0.

If |SK| = sum_i |SCC_i| with zero cone, then SK is precisely the set of
forced-recurrent configs (configs lying on some forced cycle in VC_NG).

This is a MUCH cleaner structural statement — SK is exactly the union of
non-trivial SCCs of F|_X, and Lemma C becomes:

  "If F|_X has ANY non-trivial SCC, then |union of non-trivial SCCs| ≥ 2^(n-1)."

Probe:
  - For each (ms, cycle) with |SK| > 0: verify cone = 0 (every SK node in SCC)
  - Count disjoint SCCs
  - Report (n, L, ms, num_SCCs, scc_sizes, total)

If cone is consistently 0, update the proof target.
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


def compute_sk_and_adj(ms, n, cycle, det):
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
    return remaining, adj


def tarjan_sccs(nodes, adj):
    import sys
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, len(nodes) * 3 + 1000))
    nodes_set = set(nodes)
    idx = [0]; stack = []; low = {}; ix = {}; on = {}; sccs = []
    def go(v):
        ix[v] = idx[0]; low[v] = idx[0]; idx[0] += 1
        stack.append(v); on[v] = True
        for w in adj.get(v, []):
            if w not in nodes_set: continue
            if w not in ix:
                go(w); low[v] = min(low[v], low[w])
            elif on.get(w, False):
                low[v] = min(low[v], ix[w])
        if low[v] == ix[v]:
            comp = []
            while True:
                w = stack.pop(); on[w] = False; comp.append(w)
                if w == v: break
            sccs.append(comp)
    for v in nodes:
        if v not in ix: go(v)
    sys.setrecursionlimit(old)
    return sccs


def main():
    print("=" * 100)
    print("RECURRENT-ONLY HYPOTHESIS: SK = disjoint union of non-trivial forced SCCs (cone = 0)")
    print("=" * 100)

    plan = [
        (5, [(2,2,2,2,3), (2,2,2,3,3), (2,2,2,3,4), (2,2,2,4,4),
             (2,2,3,3,3), (2,2,3,3,4), (2,3,3,3,3), (3,3,3,3,3),
             (2,2,2,2,4), (2,2,2,2,5), (2,2,2,4,5)], 17, 20, 25.0),
        (6, [(2,2,2,3,3,3), (2,2,2,3,3,4), (2,2,3,3,3,3),
             (2,2,3,3,3,4), (3,3,3,3,3,3), (2,2,2,2,3,3)], 17, 10, 40.0),
        (7, [(2,2,2,3,3,3,3), (2,2,2,3,3,3,4), (2,2,3,3,3,3,3)], 17, 5, 50.0),
        (8, [(2,2,2,3,3,3,3,3), (2,2,2,3,3,3,3,4)], 19, 3, 80.0),
    ]

    cone_nonzero = []
    results = defaultdict(list)

    for n, ms_list, L_max, max_cycles, tb in plan:
        bound = 2 ** (n - 1)
        total_trials = 0
        total_cone_zero = 0
        for ms in ms_list:
            cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=L_max,
                                      time_budget=tb, max_cycles=max_cycles)
            for cycle, movers, det in cycles:
                sk, adj = compute_sk_and_adj(ms, n, cycle, det)
                if not sk: continue
                total_trials += 1
                sccs = tarjan_sccs(list(sk), adj)
                # "In-SCC" = belongs to non-trivial SCC (size>=2 OR self-loop)
                nt_nodes = set()
                nt_sizes = []
                for s in sccs:
                    if len(s) >= 2:
                        nt_nodes.update(s); nt_sizes.append(len(s))
                    elif s[0] in adj.get(s[0], []):
                        nt_nodes.update(s); nt_sizes.append(1)
                cone = len(sk) - len(nt_nodes)
                if cone == 0:
                    total_cone_zero += 1
                else:
                    cone_nonzero.append((n, ms, len(cycle), len(sk), cone, sorted(nt_sizes, reverse=True)))
                results[n].append({
                    'ms': ms, 'L': len(cycle), 'sk': len(sk),
                    'nt_sizes': sorted(nt_sizes, reverse=True),
                    'cone': cone, 'num_scc': len(nt_sizes),
                    'bound': bound,
                })
        print(f"\n=== n={n}  bound=2^{n-1}={bound}  trials={total_trials}  "
              f"cone_zero={total_cone_zero}/{total_trials} ===")
        # Summary of (num_SCC, min_SCC, sum_SCC) stats at this n
        recs = results[n]
        if recs:
            num_scc_counter = Counter(r['num_scc'] for r in recs)
            min_scc_min = min(min(r['nt_sizes']) for r in recs if r['nt_sizes'])
            sum_scc_min = min(sum(r['nt_sizes']) for r in recs if r['nt_sizes'])
            max_cone = max(r['cone'] for r in recs)
            print(f"   num_SCC distribution: {dict(sorted(num_scc_counter.items()))}")
            print(f"   min individual SCC size (across all cycles):     {min_scc_min}")
            print(f"   min SUM of SCC sizes (across all cycles):        {sum_scc_min}")
            print(f"   max cone size observed:                          {max_cone}")
            print(f"   sum_SCC ≥ 2^{n-1}={bound}? "
                  f"{'YES ✓' if sum_scc_min >= bound else 'NO ✗'}")
            # distribution of sum_scc
            sums = sorted(set(sum(r['nt_sizes']) for r in recs))
            print(f"   distinct sum_SCC values: {sums[:12]}{'…' if len(sums)>12 else ''}")

    # Close look at cone_nonzero cases
    print("\n" + "=" * 100)
    print(f"NON-ZERO CONE CASES: {len(cone_nonzero)}")
    print("=" * 100)
    for rec in cone_nonzero[:20]:
        n, ms, L, sk_sz, cone, nts = rec
        print(f"  n={n} ms={ms} L={L} |SK|={sk_sz} cone={cone} SCC_sizes={nts}")
    if not cone_nonzero:
        print("  NONE — SK is always the union of non-trivial forced SCCs (cone=0).")


if __name__ == "__main__":
    main()
