#!/usr/bin/env python3
"""Graph-theoretic characterization of SK.

Hypothesis: SK = the set of configs in VC_NG that lie on a directed
cycle in the forced-move graph. Equivalently, SK = union of nontrivial
SCCs under move_entries restricted to VC_NG.

If true, SK is 'the strongly-connected core of the forced-move graph'.
This gives a clean characterization independent of peel iteration.

Additionally: what's the dominant SCC size in SK? If there's one huge
SCC containing most of SK, that's the 'heart' of the kernel.

Measurements:
  (1) Does VC_NG \ SK = the 'transient' configs (not on any cycle)?
  (2) |SK| vs sum of SCC sizes with size >= 2.
  (3) For each SK config c, does c actually lie on a forced-move cycle?
  (4) Conjugate: does every config in an SCC belong to SK (and vice versa)?
  (5) Sizes of SCCs in SK.
"""
from itertools import product as iproduct
from collections import Counter, defaultdict
import time
import sys


def enumerate_multisets(n, max_product):
    out = []
    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product: out.append(tuple(prefix))
            return
        for m in range(2, max_product + 1):
            new_prod = prod * m
            min_remaining = 2 ** (n - i - 1)
            if new_prod * min_remaining >= max_product: break
            prefix.append(m); rec(i + 1, prefix, new_prod); prefix.pop()
    rec(0, [], 1)
    return out


def m_n_sharp(n):
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen_cycles = set(); t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
            km = (p, Lp, Sp, Rp); forced = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced is not None and forced != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]; ki = (i,Li,Si,Ri)
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


def compute_sk(vcng_set, move_entries, n):
    current = set(vcng_set)
    while True:
        victims = set()
        for c in current:
            has_forced = False
            for p in range(n):
                ctx = (p, c[(p-1)%n], c[p], c[(p+1)%n])
                if ctx in move_entries:
                    nc = list(c); nc[p] = move_entries[ctx]; nc = tuple(nc)
                    if nc in current: has_forced = True; break
            if not has_forced: victims.add(c)
        if not victims: break
        current -= victims
    return current


def build_forced_graph(nodes, move_entries, n):
    """Build adjacency from c to forced successors within `nodes`."""
    adj = defaultdict(list)
    for c in nodes:
        for p in range(n):
            ctx = (p, c[(p-1)%n], c[p], c[(p+1)%n])
            if ctx in move_entries:
                nc = list(c); nc[p] = move_entries[ctx]; nc = tuple(nc)
                if nc in nodes:
                    adj[c].append(nc)
    return adj


def tarjan_sccs(nodes, adj):
    idx = [0]; stack = []; on_stack = {}; indices = {}; lowlink = {}; sccs = []
    def strongconnect(v):
        # iterative version for deep graphs
        call_stack = [(v, iter(adj[v]))]
        indices[v] = idx[0]; lowlink[v] = idx[0]; idx[0] += 1
        stack.append(v); on_stack[v] = True
        while call_stack:
            node, it = call_stack[-1]
            done = True
            for w in it:
                if w not in indices:
                    indices[w] = idx[0]; lowlink[w] = idx[0]; idx[0] += 1
                    stack.append(w); on_stack[w] = True
                    call_stack.append((w, iter(adj[w])))
                    done = False
                    break
                elif on_stack.get(w, False):
                    lowlink[node] = min(lowlink[node], indices[w])
            if done:
                if lowlink[node] == indices[node]:
                    scc = []
                    while True:
                        w = stack.pop(); on_stack[w] = False; scc.append(w)
                        if w == node: break
                    sccs.append(scc)
                call_stack.pop()
                if call_stack:
                    parent = call_stack[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[node])
    for v in nodes:
        if v not in indices:
            strongconnect(v)
    return sccs


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n): V[i].add(c[i])
    return V


def measure(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    fc = Counter(movers)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    SK = compute_sk(VC_NG, move_entries, n)
    if not SK: return None

    # Build forced graph on VC_NG (not just SK), to test whether SK = cycle-bearing configs
    adj_vcng = build_forced_graph(VC_NG, move_entries, n)
    sccs_vcng = tarjan_sccs(list(VC_NG), adj_vcng)
    # Nontrivial SCC = size > 1 OR size 1 with self-loop
    nontrivial_nodes = set()
    for scc in sccs_vcng:
        if len(scc) > 1:
            nontrivial_nodes.update(scc)
        elif len(scc) == 1:
            v = scc[0]
            if v in adj_vcng[v]:
                nontrivial_nodes.add(v)

    sk_eq_nontrivial = (SK == nontrivial_nodes)

    # Also build SCCs WITHIN SK for sanity
    adj_sk = build_forced_graph(SK, move_entries, n)
    sccs_sk = tarjan_sccs(list(SK), adj_sk)
    scc_sizes_sk = sorted([len(s) for s in sccs_sk], reverse=True)

    return {
        'ms': ms, 'n': n, 'L': L,
        'SK_size': len(SK),
        'VCNG_size': len(VC_NG),
        'nontrivial_nodes_in_VCNG': len(nontrivial_nodes),
        'SK_eq_nontrivial_VCNG': sk_eq_nontrivial,
        'SK_minus_nontrivial': len(SK - nontrivial_nodes),
        'nontrivial_minus_SK': len(nontrivial_nodes - SK),
        'scc_sizes_sk': scc_sizes_sk[:5],
        'n_sccs_sk': len(sccs_sk),
        'max_scc_sk': scc_sizes_sk[0] if scc_sizes_sk else 0,
        'largest_scc_frac': scc_sizes_sk[0] / len(SK) if scc_sizes_sk else 0,
    }


def main():
    sys.setrecursionlimit(50000)
    plan = [
        (5, 1, 8, 2.0, 16),
        (6, 5, 5, 3.0, 17),
        (7, 30, 3, 5.0, 18),
        (8, 300, 2, 10.0, 22),
    ]
    by_n = {}
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)[::stride]
        print(f"\n=== n={n}  {len(multisets)} multisets ===", flush=True)
        recs = []
        t0 = time.time()
        for idx, ms in enumerate(multisets):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                if len(movers) < 2*n+2: continue
                r = measure(ms, n, cycle, movers, det)
                if r is None: continue
                recs.append(r)
            if (idx+1) % max(1, len(multisets)//5) == 0:
                print(f"  [{idx+1}/{len(multisets)}] {time.time()-t0:.0f}s recs={len(recs)}", flush=True)
        by_n[n] = recs

    print(f"\n{'='*78}\nSCC characterization results\n{'='*78}")
    for n in sorted(by_n):
        recs = by_n[n]
        if not recs: continue
        total = len(recs)
        print(f"\n  n={n}  records={total}")
        eq = sum(1 for r in recs if r['SK_eq_nontrivial_VCNG'])
        print(f"  SK == nontrivial-SCCs(VC_NG):  {eq}/{total} ({100*eq/total:.1f}%)")
        # Failures: how much do they differ?
        sk_minus = [r['SK_minus_nontrivial'] for r in recs]
        nt_minus = [r['nontrivial_minus_SK'] for r in recs]
        print(f"  |SK \\ nontrivial| min/avg/max: {min(sk_minus)}/{sum(sk_minus)/total:.2f}/{max(sk_minus)}")
        print(f"  |nontrivial \\ SK| min/avg/max: {min(nt_minus)}/{sum(nt_minus)/total:.2f}/{max(nt_minus)}")
        # SCC structure of SK
        max_fracs = [r['largest_scc_frac'] for r in recs]
        n_sccs = [r['n_sccs_sk'] for r in recs]
        print(f"  largest SCC / |SK|  min/avg/max: {min(max_fracs):.3f}/{sum(max_fracs)/total:.3f}/{max(max_fracs):.3f}")
        print(f"  #SCCs in SK       min/avg/max: {min(n_sccs)}/{sum(n_sccs)/total:.1f}/{max(n_sccs)}")


if __name__ == "__main__":
    main()
