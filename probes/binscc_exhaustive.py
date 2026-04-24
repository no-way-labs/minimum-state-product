#!/usr/bin/env python3
"""binscc_exhaustive.py — Exhaustive overlap-or-SCC dichotomy test.

Test ALL distinct permutations (not just necklaces) because the bounce
pattern breaks rotational symmetry of the ring.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian, permutations
from collections import defaultdict
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


def count_binary_involutions(ms, n, det, good_set):
    binary_procs = [p for p in range(n) if ms[p] == 2]
    if not binary_procs:
        return 0
    binary_configs = list(cartesian(*([range(2)] * n)))
    binary_nongood = set(c for c in binary_configs if c not in good_set)

    count = 0
    for c in binary_nongood:
        for p in binary_procs:
            L, S, R = c[(p-1)%n], c[p], c[(p+1)%n]
            key = (p, L, S, R)
            if key not in det or det[key] == S:
                continue
            if det[key] > 1:
                continue
            c2 = list(c)
            c2[p] = 1 - S
            c2 = tuple(c2)
            if c2 not in binary_nongood:
                continue
            L2, S2, R2 = c2[(p-1)%n], c2[p], c2[(p+1)%n]
            key2 = (p, L2, S2, R2)
            if key2 in det and det[key2] == S:
                if c < c2:
                    count += 1
    return count


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


def binary_scc_count(ms, n, det, good_set):
    """Return (n_sccs, trapped) in binary subspace."""
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
    return len(sccs), sum(len(s) for s in sccs)


def full_scc_count(ms, n, det, good_set):
    """Return (n_sccs, trapped) in full config space."""
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


if __name__ == "__main__":
    n = 9
    bounce_up = list(range(n)) + list(range(n-2, 0, -1))
    bounce_dn = list(range(n-1, -1, -1)) + list(range(1, n))
    patterns = [('up-down', bounce_up), ('down-up', bounce_dn)]

    # ================================================================
    # Part 1: Exhaustive test for {2^3, 3^6}
    # ================================================================
    print("=" * 78)
    print("EXHAUSTIVE DICHOTOMY: {2^3, 3^6} at n=9")
    print("=" * 78)

    ms_sorted = (2,2,2,3,3,3,3,3,3)
    all_perms = set(permutations(ms_sorted))
    print(f"Distinct permutations: {len(all_perms)}")

    no_cycle = 0
    overlap_no_scc = 0
    scc_no_overlap = 0
    both = 0
    neither = 0
    neither_cases = []

    for perm in sorted(all_perms):
        for pname, bp in patterns:
            cycle, movers = build_bounce_cycle(perm, n, bp)
            if cycle is None:
                no_cycle += 1
                continue

            has_overlap = check_overlap(cycle, movers, n)
            det = extract_determined(cycle, movers, n)
            good_set = set(cycle)
            n_inv = count_binary_involutions(perm, n, det, good_set)
            bin_sccs, bin_trapped = binary_scc_count(perm, n, det, good_set)

            has_scc = bin_sccs > 0 or n_inv > 0

            if has_overlap and has_scc:
                both += 1
            elif has_overlap:
                overlap_no_scc += 1
            elif has_scc:
                scc_no_overlap += 1
            else:
                neither += 1
                neither_cases.append((perm, pname, len(cycle)))

    total_cycles = overlap_no_scc + scc_no_overlap + both + neither
    print(f"\nNo cycle: {no_cycle}")
    print(f"Total with cycles: {total_cycles}")
    print(f"  Overlap only: {overlap_no_scc}")
    print(f"  SCC only: {scc_no_overlap}")
    print(f"  Both: {both}")
    print(f"  NEITHER: {neither}")

    if neither == 0:
        print(f"\n*** DICHOTOMY HOLDS for all {total_cycles} cycles! ***")
    else:
        print(f"\n*** DICHOTOMY VIOLATED by {neither} cases ***")
        # Check if these have full-space SCCs
        for perm, pname, clen in neither_cases[:10]:
            bp = bounce_up if pname == 'up-down' else bounce_dn
            cycle, movers = build_bounce_cycle(perm, n, bp)
            det = extract_determined(cycle, movers, n)
            good_set = set(cycle)
            f_sccs, f_trapped = full_scc_count(perm, n, det, good_set)
            print(f"  {perm} ({pname}, cyc={clen}): "
                  f"full_SCCs={f_sccs}, full_trapped={f_trapped}")

    # ================================================================
    # Part 2: Expand: test whether FULL-SPACE forced SCCs cover all cases
    # ================================================================
    print(f"\n{'=' * 78}")
    print("FULL-SPACE DICHOTOMY: overlap OR full-space forced SCC")
    print("=" * 78)

    neither2 = 0
    neither2_cases = []

    for perm in sorted(all_perms):
        for pname, bp in patterns:
            cycle, movers = build_bounce_cycle(perm, n, bp)
            if cycle is None:
                continue

            has_overlap = check_overlap(cycle, movers, n)
            if has_overlap:
                continue  # already blocked

            det = extract_determined(cycle, movers, n)
            good_set = set(cycle)
            f_sccs, f_trapped = full_scc_count(perm, n, det, good_set)

            if f_sccs == 0:
                neither2 += 1
                neither2_cases.append((perm, pname, len(cycle)))

    if neither2 == 0:
        print(f"*** FULL-SPACE DICHOTOMY HOLDS ***")
        print(f"Every consistent bounce cycle has full-space forced SCCs.")
    else:
        print(f"Full-space dichotomy violated by {neither2} cases:")
        for perm, pname, clen in neither2_cases[:10]:
            print(f"  {perm} ({pname}, cyc={clen})")

    # ================================================================
    # Part 3: Same for {2^4, 3^5}
    # ================================================================
    print(f"\n{'=' * 78}")
    print("EXHAUSTIVE DICHOTOMY: {2^4, 3^5} at n=9")
    print("=" * 78)

    ms_sorted = (2,2,2,2,3,3,3,3,3)
    all_perms = set(permutations(ms_sorted))
    print(f"Distinct permutations: {len(all_perms)}")

    no_cycle = 0
    total_cycles = 0
    overlap_count = 0
    consistent_with_scc = 0
    consistent_no_scc = 0
    consistent_no_scc_but_full_scc = 0
    clean = 0  # consistent, no binary SCC, no full SCC

    for perm in sorted(all_perms):
        for pname, bp in patterns:
            cycle, movers = build_bounce_cycle(perm, n, bp)
            if cycle is None:
                no_cycle += 1
                continue

            total_cycles += 1
            has_overlap = check_overlap(cycle, movers, n)

            if has_overlap:
                overlap_count += 1
                continue

            det = extract_determined(cycle, movers, n)
            good_set = set(cycle)
            bin_sccs, bin_trapped = binary_scc_count(perm, n, det, good_set)

            if bin_sccs > 0:
                consistent_with_scc += 1
            else:
                f_sccs, f_trapped = full_scc_count(perm, n, det, good_set)
                if f_sccs > 0:
                    consistent_no_scc_but_full_scc += 1
                else:
                    clean += 1

    print(f"No cycle: {no_cycle}")
    print(f"Total cycles: {total_cycles}")
    print(f"  Overlap: {overlap_count}")
    print(f"  Consistent + binary SCC: {consistent_with_scc}")
    print(f"  Consistent + no bin SCC + full SCC: {consistent_no_scc_but_full_scc}")
    print(f"  CLEAN (no overlap, no forced SCC): {clean}")

    if clean == 0:
        print(f"\n*** FULL-SPACE DICHOTOMY HOLDS for 4B! ***")
    else:
        print(f"\n*** {clean} clean cases — forced SCCs do NOT explain everything ***")

    # ================================================================
    # Part 4: {2^5, 3^4}
    # ================================================================
    print(f"\n{'=' * 78}")
    print("EXHAUSTIVE DICHOTOMY: {2^5, 3^4} at n=9")
    print("=" * 78)

    ms_sorted = (2,2,2,2,2,3,3,3,3)
    all_perms = set(permutations(ms_sorted))
    print(f"Distinct permutations: {len(all_perms)}")

    no_cycle = 0
    total_cycles = 0
    overlap_count = 0
    consistent_with_scc = 0
    consistent_no_scc_full = 0
    clean = 0

    for perm in sorted(all_perms):
        for pname, bp in patterns:
            cycle, movers = build_bounce_cycle(perm, n, bp)
            if cycle is None:
                no_cycle += 1
                continue

            total_cycles += 1
            if check_overlap(cycle, movers, n):
                overlap_count += 1
                continue

            det = extract_determined(cycle, movers, n)
            good_set = set(cycle)
            bin_sccs, _ = binary_scc_count(perm, n, det, good_set)

            if bin_sccs > 0:
                consistent_with_scc += 1
            else:
                f_sccs, _ = full_scc_count(perm, n, det, good_set)
                if f_sccs > 0:
                    consistent_no_scc_full += 1
                else:
                    clean += 1

    print(f"No cycle: {no_cycle}")
    print(f"Total cycles: {total_cycles}")
    print(f"  Overlap: {overlap_count}")
    print(f"  Consistent + binary SCC: {consistent_with_scc}")
    print(f"  Consistent + no bin SCC + full SCC: {consistent_no_scc_full}")
    print(f"  CLEAN: {clean}")
    if clean == 0:
        print(f"*** FULL-SPACE DICHOTOMY HOLDS for 5B! ***")

    # ================================================================
    # Part 5: n-dependence of the dichotomy
    # ================================================================
    print(f"\n{'=' * 78}")
    print("N-DEPENDENCE: {2^3, 3^(n-3)}, all permutations")
    print("=" * 78)

    for test_n in range(5, 10):
        ms_sorted = tuple([2]*3 + [3]*(test_n-3))
        all_perms = set(permutations(ms_sorted))

        test_patterns = [
            list(range(test_n)) + list(range(test_n-2, 0, -1)),
            list(range(test_n-1, -1, -1)) + list(range(1, test_n)),
        ]

        no_cycle = 0
        total_cycles = 0
        overlap = 0
        consistent_scc = 0
        consistent_full_scc = 0
        clean = 0

        for perm in all_perms:
            for bp in test_patterns:
                cycle, movers = build_bounce_cycle(perm, test_n, bp)
                if cycle is None:
                    no_cycle += 1
                    continue

                total_cycles += 1
                if check_overlap(cycle, movers, test_n):
                    overlap += 1
                    continue

                det = extract_determined(cycle, movers, test_n)
                good_set = set(cycle)
                bin_sccs, _ = binary_scc_count(perm, test_n, det, good_set)

                if bin_sccs > 0:
                    consistent_scc += 1
                else:
                    f_sccs, _ = full_scc_count(perm, test_n, det, good_set)
                    if f_sccs > 0:
                        consistent_full_scc += 1
                    else:
                        clean += 1

        status = "HOLDS" if clean == 0 else f"VIOLATED({clean})"
        print(f"  n={test_n}: {len(all_perms)} perms, {total_cycles} cycles, "
              f"overlap={overlap}, bin_scc={consistent_scc}, "
              f"full_scc={consistent_full_scc}, clean={clean} | {status}")

    print(f"\n{'=' * 78}")
    print("DONE")
    print("=" * 78)
