#!/usr/bin/env python3
"""binscc_dichotomy.py — Verify the overlap-or-SCC dichotomy.

Key hypothesis from binscc_deep.py: For {2^3, 3^6} bounce cycles at n=9,
EVERY orientation either:
  (a) Has mover/nonmover triple overlap (cycle is inconsistent), OR
  (b) Has forced binary involution SCCs

This script verifies this dichotomy exhaustively and characterizes the
involution mechanism.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian, permutations
from collections import defaultdict
import time


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
            L = c[(p-1)%n]
            S = c[p]
            R = c[(p+1)%n]
            key = (p, L, S, R)
            det[key] = c_next[p] if p == mv else S
    return det


def check_overlap(cycle, movers, n):
    """Check if any processor sees same (L,S,R) as both mover and nonmover."""
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
    overlaps = {}
    for p in range(n):
        ov = mover_triples[p] & nonmover_triples[p]
        if ov:
            overlaps[p] = ov
    return overlaps


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


def binary_involution_analysis(ms, n, det, good_set):
    """Find forced binary involutions: pairs (c, c') differing at one binary
    processor p, where det forces p to toggle 0↔1 at both configs."""
    binary_procs = [p for p in range(n) if ms[p] == 2]
    binary_configs = list(cartesian(*([range(2)] * n)))
    binary_nongood = set(c for c in binary_configs if c not in good_set)

    involutions = []
    for c in sorted(binary_nongood):
        for p in binary_procs:
            L, S, R = c[(p-1)%n], c[p], c[(p+1)%n]
            key = (p, L, S, R)
            if key not in det or det[key] == S:
                continue
            # P forces S → 1-S at c
            c2 = list(c)
            c2[p] = 1 - S
            c2 = tuple(c2)
            if c2 not in binary_nongood:
                continue
            # Check reverse: at c2, does P force 1-S → S?
            L2, S2, R2 = c2[(p-1)%n], c2[p], c2[(p+1)%n]
            key2 = (p, L2, S2, R2)
            if key2 in det and det[key2] == S:
                if c < c2:  # avoid counting twice
                    involutions.append((c, c2, p))

    return involutions


def unique_necklaces(ms_sorted, n):
    """Generate distinct necklace representatives (rotation equivalence classes)."""
    seen = set()
    necklaces = []
    for perm in set(permutations(ms_sorted)):
        # Canonical form: lexicographically smallest rotation
        rotations = [perm[i:] + perm[:i] for i in range(n)]
        canon = min(rotations)
        if canon not in seen:
            seen.add(canon)
            necklaces.append(canon)
    return necklaces


if __name__ == "__main__":
    n = 9

    bounce_patterns = [
        ('up-down', list(range(n)) + list(range(n-2, 0, -1))),
        ('down-up', list(range(n-1, -1, -1)) + list(range(1, n))),
    ]

    # ================================================================
    # Part 1: Exhaustive dichotomy test for {2^3, 3^6}
    # ================================================================
    print("=" * 78)
    print("DICHOTOMY TEST: {2^3, 3^6} at n=9")
    print("All necklaces × both bounce patterns")
    print("=" * 78)

    ms_sorted = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    necklaces = unique_necklaces(ms_sorted, n)
    print(f"Distinct necklaces: {len(necklaces)}")

    categories = {
        'no_cycle': [],
        'overlap_only': [],
        'scc_only': [],
        'both': [],
        'neither': [],  # THE CRITICAL CASE — would disprove dichotomy
    }

    for necklace in sorted(necklaces):
        for pname, bp in bounce_patterns:
            cycle, movers = build_bounce_cycle(necklace, n, bp)
            if cycle is None:
                categories['no_cycle'].append((necklace, pname))
                continue

            # Check overlap
            overlaps = check_overlap(cycle, movers, n)
            has_overlap = len(overlaps) > 0

            # Check binary SCCs
            det = extract_determined(cycle, movers, n)
            good_set = set(cycle)
            involutions = binary_involution_analysis(necklace, n, det, good_set)
            has_scc = len(involutions) > 0

            if has_overlap and has_scc:
                categories['both'].append((necklace, pname, len(overlaps), len(involutions)))
            elif has_overlap:
                categories['overlap_only'].append((necklace, pname, overlaps))
            elif has_scc:
                categories['scc_only'].append((necklace, pname, len(involutions), len(cycle)))
            else:
                categories['neither'].append((necklace, pname, len(cycle)))

    print(f"\nResults:")
    print(f"  No cycle: {len(categories['no_cycle'])}")
    print(f"  Overlap only (cycle inconsistent): {len(categories['overlap_only'])}")
    print(f"  SCC only (consistent but trapped): {len(categories['scc_only'])}")
    print(f"  Both overlap + SCC: {len(categories['both'])}")
    print(f"  NEITHER (consistent + no SCC): {len(categories['neither'])}")

    if categories['neither']:
        print(f"\n  *** DICHOTOMY VIOLATED! ***")
        for necklace, pname, clen in categories['neither']:
            print(f"    {necklace} ({pname}), cycle_len={clen}")
    else:
        print(f"\n  *** DICHOTOMY HOLDS for {2}^3 + {3}^6! ***")
        print(f"  Every bounce cycle either overlaps or has binary involution SCCs.")

    # Show SCC-only cases
    if categories['scc_only']:
        print(f"\n  SCC-only cases (consistent cycles with forced involutions):")
        for item in categories['scc_only']:
            necklace, pname, n_inv, clen = item
            bp_positions = [i for i, m in enumerate(necklace) if m == 2]
            print(f"    {necklace} ({pname}), cyc={clen}, "
                  f"involutions={n_inv}, binary_at={bp_positions}")

    # ================================================================
    # Part 2: Repeat for more multisets
    # ================================================================
    print(f"\n{'=' * 78}")
    print("DICHOTOMY TEST: Multiple multisets")
    print("=" * 78)

    test_multisets = [
        (2,2,2,3,3,3,3,3,3),     # 3B
        (2,2,2,2,3,3,3,3,3),     # 4B
        (2,2,2,2,2,3,3,3,3),     # 5B
        (2,2,2,2,2,2,3,3,3),     # 6B
        (2,2,2,2,2,2,2,3,3),     # 7B
    ]

    for ms_sorted in test_multisets:
        nb = sum(1 for m in ms_sorted if m == 2)
        necklaces = unique_necklaces(ms_sorted, n)
        product_val = 1
        for m in ms_sorted:
            product_val *= m

        no_cycle = 0
        overlap_only = 0
        scc_only = 0
        both = 0
        neither = 0
        total_cycles = 0

        for necklace in necklaces:
            for pname, bp in bounce_patterns:
                cycle, movers = build_bounce_cycle(necklace, n, bp)
                if cycle is None:
                    no_cycle += 1
                    continue

                total_cycles += 1
                overlaps = check_overlap(cycle, movers, n)
                has_overlap = len(overlaps) > 0

                det = extract_determined(cycle, movers, n)
                good_set = set(cycle)
                involutions = binary_involution_analysis(necklace, n, det, good_set)
                has_scc = len(involutions) > 0

                if has_overlap and has_scc:
                    both += 1
                elif has_overlap:
                    overlap_only += 1
                elif has_scc:
                    scc_only += 1
                else:
                    neither += 1

        dichotomy = "HOLDS" if neither == 0 else f"VIOLATED ({neither})"
        print(f"  {ms_sorted} ({nb}B, prod={product_val}): "
              f"{len(necklaces)} necklaces, {total_cycles} cycles | "
              f"overlap={overlap_only}, SCC={scc_only}, both={both}, "
              f"neither={neither} | {dichotomy}")

    # ================================================================
    # Part 3: Involution mechanism — which processor, which context?
    # ================================================================
    print(f"\n{'=' * 78}")
    print("INVOLUTION MECHANISM: Detailed analysis")
    print("=" * 78)

    # Take the {2^3, 3^6} SCC-only cases
    for item in categories['scc_only'][:3]:
        necklace, pname, n_inv, clen = item
        bp = bounce_patterns[0][1] if pname == 'up-down' else bounce_patterns[1][1]
        cycle, movers = build_bounce_cycle(necklace, n, bp)
        det = extract_determined(cycle, movers, n)
        good_set = set(cycle)
        involutions = binary_involution_analysis(necklace, n, det, good_set)

        print(f"\n  Necklace: {necklace} ({pname}), cycle_len={clen}")
        bp_positions = [i for i, m in enumerate(necklace) if m == 2]
        print(f"  Binary processors at: {bp_positions}")
        print(f"  Involutions: {len(involutions)}")

        # Group by processor
        by_proc = defaultdict(list)
        for c, c2, p in involutions:
            by_proc[p].append((c, c2))

        for p in sorted(by_proc.keys()):
            print(f"\n    P{p} (binary): {len(by_proc[p])} involutions")
            # What contexts create the involution?
            for c, c2 in by_proc[p][:5]:
                L0, S0, R0 = c[(p-1)%n], c[p], c[(p+1)%n]
                L1, S1, R1 = c2[(p-1)%n], c2[p], c2[(p+1)%n]
                print(f"      {''.join(str(x) for x in c)} ↔ {''.join(str(x) for x in c2)}")
                print(f"        P{p} context: ({L0},{S0},{R0})→{det[(p,L0,S0,R0)]}  "
                      f"and ({L1},{S1},{R1})→{det[(p,L1,S1,R1)]}")

            # What's the context pattern?
            # For binary processor p with neighbors at p-1, p+1:
            # L = c[p-1], R = c[p+1] (both in {0,1} in binary subspace)
            # The involution requires det[(p,L,0,R)] = 1 AND det[(p,L,1,R)] = 0
            # for some L,R ∈ {0,1}
            toggle_contexts = set()
            for c, c2 in by_proc[p]:
                if c[p] == 0:
                    toggle_contexts.add((c[(p-1)%n], c[(p+1)%n]))
                else:
                    toggle_contexts.add((c2[(p-1)%n], c2[(p+1)%n]))
            print(f"      Toggle contexts (L,R): {sorted(toggle_contexts)}")

    # ================================================================
    # Part 4: N-dependence of dichotomy
    # ================================================================
    print(f"\n{'=' * 78}")
    print("N-DEPENDENCE OF DICHOTOMY: {2^3, 3^(n-3)}")
    print("=" * 78)

    for test_n in range(5, 13):
        ms_sorted = tuple([2]*3 + [3]*(test_n-3))
        necklaces = unique_necklaces(ms_sorted, test_n)

        test_bp = [
            ('up-down', list(range(test_n)) + list(range(test_n-2, 0, -1))),
            ('down-up', list(range(test_n-1, -1, -1)) + list(range(1, test_n))),
        ]

        no_cycle = 0
        overlap_only = 0
        scc_only = 0
        both = 0
        neither = 0
        max_inv = 0

        for necklace in necklaces:
            for pname, bp in test_bp:
                cycle, movers = build_bounce_cycle(necklace, test_n, bp)
                if cycle is None:
                    no_cycle += 1
                    continue

                overlaps = check_overlap(cycle, movers, test_n)
                has_overlap = len(overlaps) > 0

                det = extract_determined(cycle, movers, test_n)
                good_set = set(cycle)
                involutions = binary_involution_analysis(necklace, test_n, det, good_set)
                has_scc = len(involutions) > 0
                max_inv = max(max_inv, len(involutions))

                if has_overlap and has_scc:
                    both += 1
                elif has_overlap:
                    overlap_only += 1
                elif has_scc:
                    scc_only += 1
                else:
                    neither += 1

        total_cycles = overlap_only + scc_only + both + neither
        dichotomy = "HOLDS" if neither == 0 else f"VIOLATED({neither})"
        print(f"  n={test_n}: {len(necklaces)} necklaces, {total_cycles} cycles | "
              f"overlap={overlap_only} SCC={scc_only} both={both} "
              f"neither={neither} | max_inv={max_inv} | {dichotomy}")

    # ================================================================
    # Part 5: Can involutions at non-binary processors contribute?
    # ================================================================
    print(f"\n{'=' * 78}")
    print("NON-BINARY INVOLUTIONS: Do ternary+ processors contribute to binary SCCs?")
    print("=" * 78)

    # For ternary processor p at position p, in binary subspace context (L,S,R)
    # with L,S,R ∈ {0,1}: det[(p,L,S,R)] could be 0, 1, or 2.
    # If output is 0 or 1, it stays in binary subspace.
    # Can this create involutions?

    for item in categories['scc_only'][:2]:
        necklace, pname, n_inv, clen = item
        bp_idx = 0 if pname == 'up-down' else 1
        bp = bounce_patterns[bp_idx][1]
        cycle, movers = build_bounce_cycle(necklace, n, bp)
        det = extract_determined(cycle, movers, n)
        good_set = set(cycle)

        print(f"\n  Necklace: {necklace}")

        # Check each processor's binary-context entries
        for p in range(n):
            m_p = necklace[p]
            toggle_entries = []
            for L in range(2):
                for R in range(2):
                    key0 = (p, L, 0, R)
                    key1 = (p, L, 1, R)
                    if key0 in det and key1 in det:
                        out0 = det[key0]
                        out1 = det[key1]
                        if out0 != 0 and out0 <= 1 and out1 != 1 and out1 <= 1:
                            toggle_entries.append((L, R, out0, out1))
            if toggle_entries:
                bstr = "BINARY" if m_p == 2 else f"TERNARY(m={m_p})"
                print(f"    P{p} ({bstr}): {len(toggle_entries)} toggle contexts")
                for L, R, o0, o1 in toggle_entries:
                    print(f"      (L={L},S=0,R={R})→{o0} and (L={L},S=1,R={R})→{o1}")

    # ================================================================
    # Part 6: Full-space forced involutions (not just binary subspace)
    # ================================================================
    print(f"\n{'=' * 78}")
    print("FULL-SPACE FORCED INVOLUTIONS")
    print("=" * 78)

    # For SCC-positive orientations, how many full-space forced SCCs
    # are size 2 (involutions) vs larger?
    for item in categories['scc_only'][:3]:
        necklace, pname, n_inv, clen = item
        bp_idx = 0 if pname == 'up-down' else 1
        bp = bounce_patterns[bp_idx][1]
        cycle, movers = build_bounce_cycle(necklace, n, bp)
        det = extract_determined(cycle, movers, n)
        good_set = set(cycle)

        all_configs = list(cartesian(*(range(m) for m in necklace)))
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
        sizes = sorted([len(s) for s in sccs], reverse=True)
        size_dist = defaultdict(int)
        for s in sccs:
            size_dist[len(s)] += 1

        print(f"  {necklace} ({pname}): {len(sccs)} full SCCs, "
              f"total trapped={sum(sizes)}")
        print(f"    Size distribution: {dict(sorted(size_dist.items()))}")

        # For each SCC, identify which processors create internal edges
        if len(sccs) > 0:
            largest = max(sccs, key=len)
            scc_set_local = set(largest)
            proc_counts = defaultdict(int)
            for c in largest:
                for p in range(n):
                    L, S, R = c[(p-1)%n], c[p], c[(p+1)%n]
                    key = (p, L, S, R)
                    if key in det and det[key] != S:
                        new_c = list(c)
                        new_c[p] = det[key]
                        if tuple(new_c) in scc_set_local:
                            proc_counts[p] += 1
            print(f"    Largest SCC (size {len(largest)}), internal edge procs: "
                  f"{dict(sorted(proc_counts.items()))}")

    print(f"\n{'=' * 78}")
    print("ANALYSIS COMPLETE")
    print("=" * 78)
