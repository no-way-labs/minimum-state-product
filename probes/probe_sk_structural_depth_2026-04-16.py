#!/usr/bin/env python3
"""Speculative: structural depth of SK. Tests 4 angles:

 (1) Forman Morse check: does `move_entries` restricted to SK form an
     ACYCLIC functional graph? If yes, peel can be seen as a discrete
     gradient flow.
 (2) Hamming shells: |SK ∩ N_k(cycle)| for k=0,1,2,...  — at which k does
     2^(n-2) appear cleanly?
 (3) Double binary fc-2 slice: for records with 2+ binary fc-2 procs,
     split SK into 4 quadrants by (p1,p2). Does min quadrant ≥ 2^(n-3)?
 (4) Core vs periphery of SK: find SK's cycle structure under move_entries.
     Is the "core cycle" size a predictable invariant?
"""
from itertools import product as iproduct, combinations
from collections import Counter, defaultdict
import time


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


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n): V[i].add(c[i])
    return V


def hdist(a, b):
    return sum(1 for x, y in zip(a, b) if x != y)


def find_scc_structure(SK, move_entries, n):
    """For each SK config c, find all forced moves to SK. Build directed graph.
    Tarjan SCC — return (#SCCs, max SCC size, |nodes with in-degree 0|)."""
    adj = defaultdict(list)
    for c in SK:
        for p in range(n):
            ctx = (p, c[(p-1)%n], c[p], c[(p+1)%n])
            if ctx in move_entries:
                nc = list(c); nc[p] = move_entries[ctx]; nc = tuple(nc)
                if nc in SK:
                    adj[c].append(nc)
    # Tarjan
    idx = [0]; stack = []; on_stack = {}; indices = {}; lowlink = {}; sccs = []
    def strongconnect(v):
        indices[v] = idx[0]; lowlink[v] = idx[0]; idx[0] += 1
        stack.append(v); on_stack[v] = True
        for w in adj[v]:
            if w not in indices:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif on_stack.get(w, False):
                lowlink[v] = min(lowlink[v], indices[w])
        if lowlink[v] == indices[v]:
            scc = []
            while True:
                w = stack.pop(); on_stack[w] = False; scc.append(w)
                if w == v: break
            sccs.append(scc)
    import sys
    sys.setrecursionlimit(50000)
    for v in SK:
        if v not in indices:
            strongconnect(v)
    nontrivial = [s for s in sccs if len(s) > 1]
    total_edges = sum(len(adj[c]) for c in SK)
    return {
        'n_sccs': len(sccs),
        'max_scc': max((len(s) for s in sccs), default=0),
        'nontrivial_sccs': len(nontrivial),
        'singleton_sccs': sum(1 for s in sccs if len(s) == 1),
        'n_edges': total_edges,
    }


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

    # (2) Hamming shells: for each c in SK, min Hamming dist to cycle
    h_dist = []
    for c in SK:
        h_dist.append(min(hdist(c, a) for a in cycle))
    shell_sizes = Counter(h_dist)

    # (1) Forman-style: is move_entries (restricted to SK) a FUNCTIONAL map
    # (out-degree exactly 1)? If not, how much over 1? Check for "1-cycles"
    # (self-loops) and short cycles in the functional reduction.
    scc_info = find_scc_structure(SK, move_entries, n)

    # (3) Double binary slice
    fc2_bin = [p for p in range(n) if fc[p] == 2 and len(V[p]) == 2]
    double_slice = None
    if len(fc2_bin) >= 2:
        p1, p2 = fc2_bin[0], fc2_bin[1]
        v1 = sorted(V[p1]); v2 = sorted(V[p2])
        quads = {}
        for a in v1:
            for b in v2:
                quads[(a, b)] = sum(1 for c in SK if c[p1] == a and c[p2] == b)
        double_slice = {
            'p1': p1, 'p2': p2,
            'V_p1': v1, 'V_p2': v2,
            'quads': quads,
            'min_quad': min(quads.values()),
            'max_quad': max(quads.values()),
        }

    bound = 2 ** (n - 1)
    bound_half = 2 ** (n - 2)
    bound_quart = 2 ** (n - 3)

    return {
        'ms': ms, 'n': n, 'L': L,
        'SK_size': len(SK), 'VC_NG_size': len(VC_NG),
        'V_sizes': [len(v) for v in V],
        'shell_sizes': dict(shell_sizes),
        'max_shell_size': max(shell_sizes.values()),
        'max_shell_k': max(h_dist),
        'min_shell_k': min(h_dist),
        'scc_info': scc_info,
        'double_slice': double_slice,
        'n_fc2_bin': len(fc2_bin),
    }


def main():
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

    print(f"\n{'='*78}\nStructural depth results\n{'='*78}")
    for n in sorted(by_n):
        recs = by_n[n]
        if not recs: continue
        total = len(recs)
        bound = 2**(n-1)

        # (2) Hamming shell analysis
        all_shells = defaultdict(lambda: [])
        for r in recs:
            for k, v in r['shell_sizes'].items():
                all_shells[k].append(v)
        print(f"\n  n={n}  records={total}  bound 2^(n-1)={bound}")
        print(f"  --- (2) Hamming shells |SK ∩ N_k(cycle)|  avg over records ---")
        for k in sorted(all_shells):
            avg = sum(all_shells[k])/total
            print(f"    k={k}:  avg={avg:>7.1f}  min={min(all_shells[k]):>4}  max={max(all_shells[k]):>5}  recs_with={len(all_shells[k])}")

        # (1) SCC/Morse check
        n_sccs = [r['scc_info']['n_sccs'] for r in recs]
        max_scc = [r['scc_info']['max_scc'] for r in recs]
        nontrivial = [r['scc_info']['nontrivial_sccs'] for r in recs]
        avg_edges = sum(r['scc_info']['n_edges'] for r in recs)/total
        avg_sk = sum(r['SK_size'] for r in recs)/total
        print(f"  --- (1) SK forced-move graph structure ---")
        print(f"    avg #SCCs: {sum(n_sccs)/total:.1f}  avg max SCC: {sum(max_scc)/total:.1f}  "
              f"avg nontrivial SCCs: {sum(nontrivial)/total:.1f}")
        print(f"    avg |SK|: {avg_sk:.1f}  avg edges in SK: {avg_edges:.1f}  ratio: {avg_edges/avg_sk:.2f}")
        # SK is acyclic iff all SCCs are singletons
        acyclic = sum(1 for r in recs if r['scc_info']['nontrivial_sccs'] == 0)
        print(f"    SK acyclic under move_entries: {acyclic}/{total} ({100*acyclic/total:.1f}%)")

        # (3) Double binary slice
        dbl = [r for r in recs if r['double_slice']]
        if dbl:
            min_quads = [r['double_slice']['min_quad'] for r in dbl]
            bound_quart = 2**(n-3)
            ge = sum(1 for r in dbl if r['double_slice']['min_quad'] >= bound_quart)
            print(f"  --- (3) Double binary fc-2 slice ---")
            print(f"    records with ≥2 binary fc-2 procs: {len(dbl)}/{total}")
            print(f"    min_quadrant ≥ 2^(n-3)={bound_quart}:  {ge}/{len(dbl)} ({100*ge/max(len(dbl),1):.1f}%)")
            print(f"    min_quadrant min/avg/max: {min(min_quads)} / {sum(min_quads)/len(min_quads):.1f} / {max(min_quads)}")

        # Sample shell distribution
        print(f"  Sample shell dist (first record): {dict(sorted(recs[0]['shell_sizes'].items()))}")


if __name__ == "__main__":
    main()
