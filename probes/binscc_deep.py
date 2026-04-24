#!/usr/bin/env python3
"""binscc_deep.py — Deep analysis of binary SCC obstruction.

Key questions from v2:
1. For orientations WITHOUT binary SCCs, do full-space forced SCCs exist?
2. Can SCC-free orientations be completed to valid systems?
3. What distinguishes SCC-producing from SCC-free orientations?
4. N-dependence with proper orientation search.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
from verifier import verify_system
import time
import random

random.seed(42)


def build_bounce_cycle(ms, n, base_pattern=None, max_reps=5):
    if base_pattern is None:
        base_pattern = list(range(n)) + list(range(n-2, 0, -1))
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
            L = c[(p-1) % n]
            S = c[p]
            R = c[(p+1) % n]
            key = (p, L, S, R)
            det[key] = c_next[p] if p == mv else S
    return det


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


def binary_scc_analysis(ms, n, det, good_set):
    """Quick binary subspace SCC check."""
    binary_configs = list(cartesian(*([range(2)] * n)))
    binary_nongood = [c for c in binary_configs if c not in good_set]
    binary_nongood_set = set(binary_nongood)

    forced_adj = defaultdict(list)
    for c in binary_nongood:
        for p in range(n):
            L = c[(p-1) % n]
            S = c[p]
            R = c[(p+1) % n]
            key = (p, L, S, R)
            if key in det and det[key] != S and det[key] <= 1:
                new_c = list(c)
                new_c[p] = det[key]
                new_c = tuple(new_c)
                if new_c in binary_nongood_set:
                    forced_adj[c].append(new_c)

    sccs = find_sccs(dict(forced_adj))
    return sum(len(s) for s in sccs), len(sccs)


def full_forced_scc_analysis(ms, n, det, good_set):
    """Full-space forced SCC analysis."""
    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    forced_adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            L = c[(p-1) % n]
            S = c[p]
            R = c[(p+1) % n]
            key = (p, L, S, R)
            if key in det and det[key] != S:
                new_c = list(c)
                new_c[p] = det[key]
                new_c = tuple(new_c)
                if new_c in non_good_set:
                    forced_adj[c].append(new_c)

    sccs = find_sccs(dict(forced_adj))
    trapped = sum(len(s) for s in sccs)

    # Classify: how many SCC configs are all-binary?
    binary_in_scc = 0
    for scc in sccs:
        for c in scc:
            if all(v <= 1 for v in c):
                binary_in_scc += 1

    return trapped, len(sccs), binary_in_scc


def try_good_targeting_completion(ms, n, cycle, movers):
    """Try good-targeting completion. Return (valid, scc_count_in_bad)."""
    good_set = set(cycle)
    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    det = extract_determined(cycle, movers, n)

    # Free entries
    free_entries = []
    for p in range(n):
        m_L = ms[(p-1) % n]
        m_S = ms[p]
        m_R = ms[(p+1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in det:
                        free_entries.append(key)

    # Check triple overlap
    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    for idx in range(len(cycle)):
        c = cycle[idx]
        mv = movers[idx]
        for p in range(n):
            triple = (c[(p-1) % n], c[p], c[(p+1) % n])
            if p == mv:
                mover_triples[p].add(triple)
            else:
                nonmover_triples[p].add(triple)
    for p in range(n):
        if mover_triples[p] & nonmover_triples[p]:
            return None, None, "overlap"

    # Edge costs
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

    # Good-targeting
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

    # Liveness fix
    for c in all_configs:
        has_priv = any(comp.get((p, c[(p-1)%n], c[p], c[(p+1)%n]), c[p]) != c[p]
                       for p in range(n))
        if not has_priv:
            best_key, best_cost, best_out_val = None, float('inf'), None
            for p in range(n):
                L2, S2, R2 = c[(p-1)%n], c[p], c[(p+1)%n]
                key = (p, L2, S2, R2)
                if key not in det:
                    for out in range(ms[p]):
                        if out != S2:
                            cost = edge_costs.get((key, out), 0)
                            if cost < best_cost:
                                best_cost, best_key, best_out_val = cost, key, out
            if best_key:
                comp[best_key] = best_out_val

    # Build fs and check SCCs in bad graph
    def make_f(p_idx):
        def f(L, S, R):
            return comp.get((p_idx, L, S, R), S)
        return f
    fs = [make_f(p) for p in range(n)]

    # Count bad SCCs
    bad_adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            L, S, R = c[(p-1)%n], c[p], c[(p+1)%n]
            new_S = comp.get((p, L, S, R), S)
            if new_S != S:
                new_c = list(c)
                new_c[p] = new_S
                new_c = tuple(new_c)
                if new_c in non_good_set:
                    bad_adj[c].append(new_c)
    bad_sccs = find_sccs(dict(bad_adj))
    bad_trapped = sum(len(s) for s in bad_sccs)

    # Full verification
    result = verify_system(list(ms), fs, verbose=False)
    return result['valid'], bad_trapped, "ok"


if __name__ == "__main__":
    n = 9
    bounce_patterns = [
        ('up-down', lambda n: list(range(n)) + list(range(n-2, 0, -1))),
        ('down-up', lambda n: list(range(n-1, -1, -1)) + list(range(1, n))),
    ]

    # ================================================================
    # Part 1: For 3B {2,2,2,3,3,3,3,3,3}, characterize SCC vs no-SCC
    # ================================================================
    print("=" * 78)
    print("PART 1: Characterizing SCC vs no-SCC orientations for {2^3, 3^6}")
    print("=" * 78)

    ms_sorted = (2,2,2,3,3,3,3,3,3)

    # Generate many orientations
    all_orients = set()
    for _ in range(500):
        perm = list(ms_sorted)
        random.shuffle(perm)
        all_orients.add(tuple(perm))

    scc_orients = []
    noscc_orients = []

    for orient in sorted(all_orients):
        for pname, pfunc in bounce_patterns:
            bp = pfunc(n)
            cycle, movers = build_bounce_cycle(orient, n, bp)
            if cycle is None:
                continue

            det = extract_determined(cycle, movers, n)
            good_set = set(cycle)
            trapped, nscc = binary_scc_analysis(orient, n, det, good_set)

            if nscc > 0:
                scc_orients.append((orient, pname, trapped, nscc, len(cycle)))
            else:
                noscc_orients.append((orient, pname, len(cycle)))

    print(f"Total orientations with cycles: {len(scc_orients) + len(noscc_orients)}")
    print(f"  With binary SCCs: {len(scc_orients)}")
    print(f"  Without binary SCCs: {len(noscc_orients)}")

    # Characterize: what's the binary position pattern?
    def binary_positions(ms):
        return tuple(i for i, m in enumerate(ms) if m == 2)

    def consecutive_binary_runs(ms):
        n = len(ms)
        runs = []
        cur = 0
        for i in range(n):
            if ms[i] == 2:
                cur += 1
            else:
                if cur > 0:
                    runs.append(cur)
                cur = 0
        if cur > 0:
            # Check wrap-around
            if runs and ms[0] == 2:
                runs[0] += cur
            else:
                runs.append(cur)
        return tuple(sorted(runs, reverse=True))

    scc_run_patterns = defaultdict(int)
    noscc_run_patterns = defaultdict(int)

    for orient, pname, trapped, nscc, clen in scc_orients:
        pattern = consecutive_binary_runs(orient)
        scc_run_patterns[pattern] += 1

    for orient, pname, clen in noscc_orients:
        pattern = consecutive_binary_runs(orient)
        noscc_run_patterns[pattern] += 1

    print(f"\n  SCC orientations — binary run patterns:")
    for pat, count in sorted(scc_run_patterns.items()):
        print(f"    {pat}: {count}")

    print(f"\n  No-SCC orientations — binary run patterns:")
    for pat, count in sorted(noscc_run_patterns.items()):
        print(f"    {pat}: {count}")

    # ================================================================
    # Part 2: For SCC-free 3B orientations, try completion
    # ================================================================
    print(f"\n{'=' * 78}")
    print("PART 2: Can SCC-free 3B orientations be completed to valid systems?")
    print("=" * 78)

    tested = 0
    valid_count = 0
    scc_after_completion = 0

    for orient, pname, clen in noscc_orients[:20]:
        bp = bounce_patterns[0][1](n) if pname == 'up-down' else bounce_patterns[1][1](n)
        cycle, movers = build_bounce_cycle(orient, n, bp)
        if cycle is None:
            continue

        t0 = time.time()
        valid, bad_trapped, status = try_good_targeting_completion(orient, n, cycle, movers)
        elapsed = time.time() - t0
        tested += 1

        if status == "overlap":
            print(f"  {orient} ({pname}): OVERLAP")
            continue

        if valid:
            valid_count += 1
            print(f"  {orient} ({pname}): VALID! [{elapsed:.1f}s]")
        else:
            if bad_trapped and bad_trapped > 0:
                scc_after_completion += 1
            print(f"  {orient} ({pname}): INVALID (bad_sccs_trapped={bad_trapped}) [{elapsed:.1f}s]")

    print(f"\n  Tested: {tested}, Valid: {valid_count}, "
          f"SCCs after completion: {scc_after_completion}")

    # ================================================================
    # Part 3: Full forced SCC for SCC-free binary orientations
    # ================================================================
    print(f"\n{'=' * 78}")
    print("PART 3: Full-space forced SCCs for binary-SCC-free orientations")
    print("=" * 78)

    for orient, pname, clen in noscc_orients[:10]:
        bp = bounce_patterns[0][1](n) if pname == 'up-down' else bounce_patterns[1][1](n)
        cycle, movers = build_bounce_cycle(orient, n, bp)
        if cycle is None:
            continue

        det = extract_determined(cycle, movers, n)
        good_set = set(cycle)
        full_trapped, full_nscc, bin_in = full_forced_scc_analysis(orient, n, det, good_set)

        print(f"  {orient} ({pname}, cyc={clen}): "
              f"full_SCCs={full_nscc}, trapped={full_trapped}, binary_in={bin_in}")

    # ================================================================
    # Part 4: SCC orientations — full forced SCC analysis
    # ================================================================
    print(f"\n{'=' * 78}")
    print("PART 4: Full-space forced SCCs for binary-SCC-POSITIVE orientations")
    print("=" * 78)

    for orient, pname, trapped, nscc, clen in scc_orients[:10]:
        bp = bounce_patterns[0][1](n) if pname == 'up-down' else bounce_patterns[1][1](n)
        cycle, movers = build_bounce_cycle(orient, n, bp)
        if cycle is None:
            continue

        det = extract_determined(cycle, movers, n)
        good_set = set(cycle)
        full_trapped, full_nscc, bin_in = full_forced_scc_analysis(orient, n, det, good_set)

        print(f"  {orient} ({pname}, cyc={clen}): "
              f"bin_SCCs={nscc}(trapped={trapped}), "
              f"full_SCCs={full_nscc}(trapped={full_trapped}, binary={bin_in})")

    # ================================================================
    # Part 5: N-dependence with orientation search
    # ================================================================
    print(f"\n{'=' * 78}")
    print("PART 5: N-dependence — 3 binary + (n-3) ternary, orientation search")
    print("=" * 78)

    for test_n in range(5, 13):
        ms_test = tuple([2]*3 + [3]*(test_n-3))
        product_val = 8 * (3**(test_n-3))

        # Generate orientations
        orients = set()
        for _ in range(200):
            perm = list(ms_test)
            random.shuffle(perm)
            orients.add(tuple(perm))

        cycle_count = 0
        scc_count = 0
        noscc_count = 0
        max_trapped = 0

        for orient in sorted(orients):
            for pname, pfunc in bounce_patterns:
                bp = pfunc(test_n)
                cycle, movers = build_bounce_cycle(orient, test_n, bp)
                if cycle is None:
                    continue

                cycle_count += 1
                det = extract_determined(cycle, movers, test_n)
                good_set = set(cycle)
                trapped, nscc = binary_scc_analysis(orient, test_n, det, good_set)

                if nscc > 0:
                    scc_count += 1
                    max_trapped = max(max_trapped, trapped)
                else:
                    noscc_count += 1

        if cycle_count == 0:
            print(f"  n={test_n}: {ms_test} prod={product_val} — no cycles from {len(orients)} orientations")
        else:
            pct = scc_count / cycle_count * 100 if cycle_count else 0
            print(f"  n={test_n}: {ms_test} prod={product_val}, "
                  f"{cycle_count} cycles, SCC={scc_count} ({pct:.0f}%), "
                  f"noSCC={noscc_count}, max_trapped={max_trapped}")

    # ================================================================
    # Part 6: Key diagnostic — what makes a binary SCC?
    # ================================================================
    print(f"\n{'=' * 78}")
    print("PART 6: Anatomy of a binary SCC (3B case, n=9)")
    print("=" * 78)

    # Take the first SCC-positive orientation and analyze its SCC in detail
    if scc_orients:
        orient, pname, trapped, nscc, clen = scc_orients[0]
        bp = bounce_patterns[0][1](n) if pname == 'up-down' else bounce_patterns[1][1](n)
        cycle, movers = build_bounce_cycle(orient, n, bp)
        det = extract_determined(cycle, movers, n)
        good_set = set(cycle)

        binary_configs = list(cartesian(*([range(2)] * n)))
        binary_nongood = [c for c in binary_configs if c not in good_set]
        binary_nongood_set = set(binary_nongood)

        forced_adj = defaultdict(list)
        for c in binary_nongood:
            for p in range(n):
                L, S, R = c[(p-1)%n], c[p], c[(p+1)%n]
                key = (p, L, S, R)
                if key in det and det[key] != S and det[key] <= 1:
                    new_c = list(c)
                    new_c[p] = det[key]
                    new_c = tuple(new_c)
                    if new_c in binary_nongood_set:
                        forced_adj[c].append(new_c)

        sccs = find_sccs(dict(forced_adj))

        print(f"  Orient: {orient} ({pname}), cycle_len={clen}")
        print(f"  Binary positions: {binary_positions(orient)}")
        print(f"  Binary non-good: {len(binary_nongood)}")
        print(f"  SCCs: {len(sccs)}, sizes: {sorted([len(s) for s in sccs], reverse=True)[:20]}")

        # Show first 3 SCCs in detail
        for i, scc in enumerate(sccs[:3]):
            scc_set_local = set(scc)
            print(f"\n  SCC[{i}] (size {len(scc)}):")
            for c in sorted(scc):
                # Find forced moves
                moves = []
                for p in range(n):
                    L, S, R = c[(p-1)%n], c[p], c[(p+1)%n]
                    key = (p, L, S, R)
                    if key in det and det[key] != S and det[key] <= 1:
                        new_c = list(c)
                        new_c[p] = det[key]
                        tgt = tuple(new_c)
                        in_scc = "→SCC" if tgt in scc_set_local else "→out"
                        moves.append(f"P{p}:{S}→{det[key]}({in_scc})")
                print(f"    {''.join(str(x) for x in c)} [{', '.join(moves)}]")

        # Analyze which processors create the SCC edges
        print(f"\n  Processor involvement in SCC edges:")
        proc_edge_count = defaultdict(int)
        proc_is_binary = {}
        for scc in sccs:
            scc_set_local = set(scc)
            for c in scc:
                for p in range(n):
                    L, S, R = c[(p-1)%n], c[p], c[(p+1)%n]
                    key = (p, L, S, R)
                    if key in det and det[key] != S and det[key] <= 1:
                        new_c = list(c)
                        new_c[p] = det[key]
                        if tuple(new_c) in scc_set_local:
                            proc_edge_count[p] += 1
                            proc_is_binary[p] = (orient[p] == 2)

        for p in sorted(proc_edge_count.keys()):
            bstr = "BINARY" if proc_is_binary[p] else f"m={orient[p]}"
            print(f"    P{p} ({bstr}): {proc_edge_count[p]} internal SCC edges")

    print(f"\n{'=' * 78}")
    print("DONE")
    print("=" * 78)
