#!/usr/bin/env python3
"""Gap mechanism probe: what's the structure forcing |SK| ≥ 2^(n-1) when > 0?

Gap dichotomy confirmed: |SK| ∈ {0} ∪ [2^(n-1), ∞). Why?

Hypotheses to check:
  H1: SK is a union of orbits under a 2^(n-1)-element group action
      → |SK| divisible by 2^(n-1) or some factor
  H2: SK is closed under some involution with free action
      → |SK| is even
  H3: SK = union of k disjoint forced-cycles, each carrying 2^(n-?) cloud
      → structural decomposition visible
  H4: SK is a union of "bit-flip cosets" from a distinguished subgroup
      → partition SK into 2^(n-1)-cosets of ∏V

For each non-zero SK observed:
  - Compute |SK| mod 2^(n-1), 2^(n-2), ..., 2
  - Check closure under candidate involutions (single flips, paired flips,
    ring shift, etc.)
  - Count distinct forced-SCCs within SK
"""
from itertools import product as iproduct, combinations
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
    return remaining, adj, V_sorted


def find_sccs(nodes, adj):
    """Tarjan SCC on induced subgraph (nodes, adj restricted to nodes)."""
    nodes_set = set(nodes)
    index_counter = [0]
    stack = []
    lowlink = {}
    index = {}
    on_stack = {}
    sccs = []

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack[v] = True
        for w in adj.get(v, []):
            if w not in nodes_set: continue
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif on_stack.get(w, False):
                lowlink[v] = min(lowlink[v], index[w])
        if lowlink[v] == index[v]:
            component = []
            while True:
                w = stack.pop()
                on_stack[w] = False
                component.append(w)
                if w == v: break
            sccs.append(component)

    import sys
    old_limit = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old_limit, len(nodes) * 3 + 1000))
    for v in nodes:
        if v not in index:
            strongconnect(v)
    sys.setrecursionlimit(old_limit)
    return sccs


def analyze_sk(n, sk, adj, V_sorted, ms):
    """Structural analysis of a non-empty SK."""
    if not sk:
        return None
    sz = len(sk)

    # H1: divisibility by powers of 2
    divs = {}
    for k in range(1, n + 1):
        d = 2 ** k
        divs[d] = (sz % d == 0)

    # H2: closure under single coord flip (only for binary positions)
    binary_positions = [p for p, m in enumerate(ms) if m == 2]
    flip_closure = {}
    for p_star in binary_positions:
        v0, v1 = sorted(V_sorted[p_star]) if len(V_sorted[p_star]) == 2 else (None, None)
        if v0 is None: continue
        closed = True
        count_paired = 0
        count_lone = 0
        for c in sk:
            tc = list(c); tc[p_star] = v1 if c[p_star] == v0 else v0; tc = tuple(tc)
            if tc in sk: count_paired += 1
            else:
                closed = False
                count_lone += 1
        flip_closure[p_star] = {
            'closed': closed,
            'paired': count_paired, 'lone': count_lone,
            'frac_paired': count_paired / sz if sz else 0
        }

    # H3: SCC structure within SK
    sccs = find_sccs(list(sk), adj)
    scc_sizes = sorted([len(s) for s in sccs], reverse=True)
    # non-trivial SCCs: those with cycles (size >=2 or a self-loop)
    non_trivial = [s for s in sccs if len(s) >= 2]
    # Of SCCs of size 1, which have self-loops?
    selfloops = sum(1 for s in sccs if len(s) == 1 and s[0] in adj.get(s[0], []))

    return {
        'size': sz,
        'divs_pow2': divs,
        'binary_flips': flip_closure,
        'num_sccs': len(sccs),
        'num_nontrivial_sccs': len(non_trivial),
        'scc_sizes_top': scc_sizes[:8],
        'selfloops': selfloops,
    }


def main():
    print("=" * 100)
    print("GAP MECHANISM PROBE: what structure forces |SK| ≥ 2^(n-1) when > 0?")
    print("=" * 100)

    # Focus on small-to-medium n with good mix of ms
    plan = [
        (5, [(2,2,2,2,3), (2,2,2,3,3), (2,2,2,3,4), (2,2,2,4,4),
             (2,2,3,3,3), (2,2,3,3,4), (2,3,3,3,3)], 17, 10, 20.0),
        (6, [(2,2,2,3,3,3), (2,2,2,3,3,4), (2,2,3,3,3,3),
             (2,2,3,3,3,4)], 17, 5, 30.0),
        (7, [(2,2,2,3,3,3,3), (2,2,2,3,3,3,4)], 17, 3, 30.0),
    ]

    all_analyses = []
    for n, ms_list, L_max, max_cycles, tb in plan:
        bound = 2 ** (n - 1)
        print(f"\n=== n={n}  bound={bound}  max_cycles={max_cycles} ===")
        for ms in ms_list:
            prod = math.prod(ms)
            cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=L_max,
                                      time_budget=tb, max_cycles=max_cycles)
            print(f"  ms={ms!s:30s} prod={prod}  found {len(cycles)} cycles")
            for ci, (cycle, movers, det) in enumerate(cycles):
                sk, adj, V_sorted = compute_sk_and_adj(ms, n, cycle, det)
                if not sk:
                    print(f"    cycle[{ci}] L={len(cycle)}: |SK|=0")
                    continue
                analysis = analyze_sk(n, sk, adj, V_sorted, ms)
                analysis['n'] = n; analysis['ms'] = ms; analysis['L'] = len(cycle)
                all_analyses.append(analysis)
                # Short printout
                sz = analysis['size']
                pow2_max = max((k for k in range(n+1) if analysis['divs_pow2'].get(2**k, False)),
                               default=0)
                nt = analysis['num_nontrivial_sccs']
                top_scc = analysis['scc_sizes_top'][:3]
                print(f"    cycle[{ci}] L={len(cycle)}: |SK|={sz}  "
                      f"max_2pow_divides=2^{pow2_max}  "
                      f"#SCC={analysis['num_sccs']} #nontrivial={nt} "
                      f"top_SCC_sizes={top_scc}")

    # Summary
    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)

    # H1: divisibility
    print("\nH1: divisibility of |SK| by 2^k (across all non-empty SK observations)")
    by_n = defaultdict(list)
    for a in all_analyses:
        by_n[a['n']].append(a)
    for n in sorted(by_n):
        bound_k = n - 1
        divs_count = Counter()
        for a in by_n[n]:
            for k in range(1, n + 1):
                if a['divs_pow2'].get(2**k, False):
                    divs_count[k] += 1
        total = len(by_n[n])
        print(f"  n={n}  total_non_empty_SK={total}  bound=2^{bound_k}")
        for k in range(1, n + 1):
            pct = 100 * divs_count[k] / total if total else 0
            flag = " <<<" if k == bound_k else ""
            print(f"    2^{k}={2**k:<5} divides |SK|  {divs_count[k]}/{total} ({pct:.0f}%){flag}")

    # H3: # non-trivial SCCs distribution
    print("\nH3: # non-trivial SCCs within SK")
    for n in sorted(by_n):
        counts = Counter(a['num_nontrivial_sccs'] for a in by_n[n])
        print(f"  n={n}  SCC count distribution: {dict(sorted(counts.items()))}")
        sizes_all = [tuple(a['scc_sizes_top'][:4]) for a in by_n[n]]
        top_sizes_counter = Counter(sizes_all)
        print(f"    most common top-4 SCC sizes: {dict(top_sizes_counter.most_common(5))}")

    # H2: binary flip closure frequency
    print("\nH2: single-binary-flip closure frequency")
    for n in sorted(by_n):
        total_checks = 0
        total_closed = 0
        for a in by_n[n]:
            for p, info in a['binary_flips'].items():
                total_checks += 1
                if info['closed']: total_closed += 1
        pct = 100 * total_closed / total_checks if total_checks else 0
        print(f"  n={n}  {total_closed}/{total_checks} "
              f"(p, cycle) pairs have SK closed under τ_p ({pct:.0f}%)")


if __name__ == "__main__":
    main()
