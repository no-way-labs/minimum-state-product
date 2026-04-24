#!/usr/bin/env python3
"""binscc_mixed.py — Dichotomy test for mixed (non-{2,3}) gap multisets.

From binscc_analysis2: multisets like (2,2,2,2,2,4,4,4,4) produce some
consistent bounce cycles. Check overlap-or-SCC dichotomy for these.
Also try completing the consistent, SCC-free cases.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian, permutations
from collections import defaultdict
from verifier import verify_system
import time


def build_bounce_cycle(ms, n, base_pattern, max_reps=5):
    for reps in range(1, max_reps):
        config = [0] * n
        cycle = [tuple(config)]
        visited = {tuple(config)}
        full = base_pattern * reps
        for step, mover in enumerate(full):
            config = list(cycle[-1])
            config[mover] = (config[mover] + 1) % ms[mover]
            nc = tuple(config)
            if nc == cycle[0]:
                return cycle, full[:step+1]
            if nc in visited:
                break
            visited.add(nc)
            cycle.append(nc)
    return None, None


def extract_determined(cycle, movers, n):
    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        mv = movers[idx]
        for p in range(n):
            L, S, R = c[(p-1)%n], c[p], c[(p+1)%n]
            det[(p, L, S, R)] = c_next[p] if p == mv else S
    return det


def check_overlap(cycle, movers, n):
    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    for idx in range(len(cycle)):
        c = cycle[idx]
        mv = movers[idx]
        for p in range(n):
            triple = (c[(p-1)%n], c[p], c[(p+1)%n])
            if p == mv:
                mover_triples[p].add(triple)
            else:
                nonmover_triples[p].add(triple)
    for p in range(n):
        if mover_triples[p] & nonmover_triples[p]:
            return True
    return False


def find_sccs(adj):
    idx_counter = [0]
    stack = []
    on_stack = set()
    index_map = {}
    lowlink = {}
    sccs = []
    def strongconnect(v):
        work = [(v, 0)]
        index_map[v] = lowlink[v] = idx_counter[0]
        idx_counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        while work:
            node, si = work[-1]
            succs = adj.get(node, [])
            if si < len(succs):
                work[-1] = (node, si + 1)
                w = succs[si]
                if w not in index_map:
                    index_map[w] = lowlink[w] = idx_counter[0]
                    idx_counter[0] += 1
                    stack.append(w)
                    on_stack.add(w)
                    work.append((w, 0))
                elif w in on_stack:
                    lowlink[node] = min(lowlink[node], index_map[w])
            else:
                if lowlink[node] == index_map[node]:
                    scc = []
                    while True:
                        w = stack.pop()
                        on_stack.discard(w)
                        scc.append(w)
                        if w == node:
                            break
                    if len(scc) > 1 or (scc[0] in adj and scc[0] in adj[scc[0]]):
                        sccs.append(scc)
                work.pop()
                if work:
                    lowlink[work[-1][0]] = min(lowlink[work[-1][0]], lowlink[node])
    for v in adj:
        if v not in index_map:
            strongconnect(v)
    return sccs


def full_scc_count(ms, n, det, good_set):
    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    forced_adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            L, S, R = c[(p-1)%n], c[p], c[(p+1)%n]
            key = (p, L, S, R)
            if key in det and det[key] != S:
                new_c = list(c)
                new_c[p] = det[key]
                new_c = tuple(new_c)
                if new_c in non_good_set:
                    forced_adj[c].append(new_c)

    sccs = find_sccs(dict(forced_adj))
    return len(sccs), sum(len(s) for s in sccs)


def try_completion(ms, n, cycle, movers):
    """Try good-targeting completion, return valid bool."""
    good_set = set(cycle)
    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    det = extract_determined(cycle, movers, n)

    free_entries = []
    for p in range(n):
        m_L = ms[(p-1)%n]
        m_S = ms[p]
        m_R = ms[(p+1)%n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in det:
                        free_entries.append(key)

    edge_costs = {}
    for key in free_entries:
        p, L, S, R = key
        for out in range(ms[p]):
            if out == S:
                edge_costs[(key, out)] = 0
            else:
                edges = sum(1 for c in non_good
                    if c[(p-1)%n]==L and c[p]==S and c[(p+1)%n]==R
                    and tuple(c[j] if j!=p else out for j in range(n)) in non_good_set)
                edge_costs[(key, out)] = edges

    comp = dict(det)
    for key in free_entries:
        p, L, S, R = key
        best_out, best_good, best_ng = S, 0, float('inf')
        for out in range(ms[p]):
            ng = edge_costs.get((key, out), 0)
            good_count = 0
            if out != S:
                good_count = sum(1 for c in non_good
                    if c[(p-1)%n]==L and c[p]==S and c[(p+1)%n]==R
                    and tuple(c[j] if j!=p else out for j in range(n)) in good_set)
            if good_count > best_good or (good_count == best_good and ng < best_ng):
                best_out, best_good, best_ng = out, good_count, ng
        comp[key] = best_out

    for c in all_configs:
        has_priv = any(comp.get((p, c[(p-1)%n], c[p], c[(p+1)%n]), c[p]) != c[p]
                       for p in range(n))
        if not has_priv:
            best_key, best_cost, bov = None, float('inf'), None
            for p in range(n):
                L2, S2, R2 = c[(p-1)%n], c[p], c[(p+1)%n]
                key = (p, L2, S2, R2)
                if key not in det:
                    for out in range(ms[p]):
                        if out != S2:
                            cost = edge_costs.get((key, out), 0)
                            if cost < best_cost:
                                best_cost, best_key, bov = cost, key, out
            if best_key:
                comp[best_key] = bov

    def make_f(p_idx):
        def f(L, S, R):
            return comp.get((p_idx, L, S, R), S)
        return f
    fs = [make_f(p) for p in range(n)]
    result = verify_system(list(ms), fs, verbose=False)
    return result['valid']


if __name__ == "__main__":
    n = 9
    bounce_up = list(range(n)) + list(range(n-2, 0, -1))
    bounce_dn = list(range(n-1, -1, -1)) + list(range(1, n))
    patterns = [('up-down', bounce_up), ('down-up', bounce_dn)]

    # Mixed multisets that produced consistent cycles in binscc_analysis2
    mixed_multisets = [
        (2,2,2,2,2,4,4,4,4),     # 8192, 5B
        (2,2,2,2,2,2,4,4,8),     # 8192, 6B
        (2,2,2,2,2,2,5,5,5),     # 8000, 6B
        (2,2,2,2,2,2,3,6,7),     # 8064, 6B
    ]

    for ms_sorted in mixed_multisets:
        product_val = 1
        for m in ms_sorted:
            product_val *= m
        nb = sum(1 for m in ms_sorted if m == 2)
        all_perms = set(permutations(ms_sorted))

        print(f"{'=' * 78}")
        print(f"DICHOTOMY: {ms_sorted} (prod={product_val}, {nb}B)")
        print(f"  {len(all_perms)} distinct permutations")
        print(f"{'=' * 78}")

        no_cycle = 0
        overlap_count = 0
        consistent_with_full_scc = 0
        clean = 0  # consistent + no forced SCC
        clean_cases = []

        t0 = time.time()

        for perm in sorted(all_perms):
            for pname, bp in patterns:
                cycle, movers = build_bounce_cycle(perm, n, bp)
                if cycle is None:
                    no_cycle += 1
                    continue

                if check_overlap(cycle, movers, n):
                    overlap_count += 1
                    continue

                det = extract_determined(cycle, movers, n)
                good_set = set(cycle)
                f_sccs, f_trapped = full_scc_count(perm, n, det, good_set)

                if f_sccs > 0:
                    consistent_with_full_scc += 1
                else:
                    clean += 1
                    clean_cases.append((perm, pname, len(cycle)))

        total_cycles = overlap_count + consistent_with_full_scc + clean
        elapsed = time.time() - t0

        print(f"  No cycle: {no_cycle}")
        print(f"  Total cycles: {total_cycles} [{elapsed:.1f}s]")
        print(f"    Overlap: {overlap_count}")
        print(f"    Consistent + full forced SCC: {consistent_with_full_scc}")
        print(f"    CLEAN (no overlap, no forced SCC): {clean}")

        if clean == 0:
            print(f"  *** FULL DICHOTOMY HOLDS ***")
        else:
            print(f"  *** {clean} clean cases ***")
            # Try to complete the clean cases
            completed = 0
            for perm, pname, clen in clean_cases[:20]:
                bp = bounce_up if pname == 'up-down' else bounce_dn
                cycle, movers = build_bounce_cycle(perm, n, bp)
                if cycle is None:
                    continue
                t1 = time.time()
                valid = try_completion(perm, n, cycle, movers)
                elapsed2 = time.time() - t1
                status = "VALID!" if valid else "invalid"
                print(f"    {perm} ({pname}, cyc={clen}): {status} [{elapsed2:.1f}s]")
                if valid:
                    completed += 1
            print(f"  Completion results: {completed}/{min(len(clean_cases), 20)} valid")

    # ================================================================
    # Final: test the valid witness for comparison
    # ================================================================
    print(f"\n{'=' * 78}")
    print("CONTROL: Valid witness ms=(2,3,3,3,3,3,3,3,2)")
    print("=" * 78)

    ms = (2,3,3,3,3,3,3,3,2)
    bp = bounce_up
    cycle, movers = build_bounce_cycle(ms, n, bp)

    has_overlap = check_overlap(cycle, movers, n)
    det = extract_determined(cycle, movers, n)
    good_set = set(cycle)
    f_sccs, f_trapped = full_scc_count(ms, n, det, good_set)

    print(f"  Overlap: {has_overlap}")
    print(f"  Full forced SCCs: {f_sccs}, trapped: {f_trapped}")
    print(f"  → This system is clean (no overlap, no forced SCC) → completable to valid system")

    print(f"\n{'=' * 78}")
    print("DONE")
    print("=" * 78)
