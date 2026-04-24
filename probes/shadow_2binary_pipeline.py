#!/usr/bin/env python3
"""shadow_2binary_pipeline.py — Run DFS pipeline on product 8748.

Tests whether non-uniform-sweep cycles can escape the 3 bad SCCs
that block all uniform sweep cycles.

For each of the 4 necklaces of {2,2,3^7}, runs:
1. DFS good-cycle search (10s per orientation)
2. Screening: check for bad SCCs in forced-move graph
3. If any survive screening, try SMT completion
"""

import sys
import os
import time
from itertools import product as cartesian
from collections import Counter

sys.path.insert(0, os.path.dirname(__file__))

from p2_good_cycle_search import enumerate_good_cycles, search_good_cycle
from p2_cycle_screen import forced_rule_map
from p2_completion_search import has_fatal_forced_cycle_singletons
from p2_ring import verify_system, RingSystem


def prod(sc):
    p = 1
    for m in sc:
        p *= m
    return p


def necklaces_2binary(n):
    """Generate all distinct necklaces for 2 identical binary items in n positions."""
    seen = set()
    necklaces = []
    for i in range(n):
        for j in range(i + 1, n):
            ms = [3] * n
            ms[i] = 2
            ms[j] = 2
            canonical = None
            for rot in range(n):
                rotated = tuple(ms[(k + rot) % n] for k in range(n))
                if canonical is None or rotated < canonical:
                    canonical = rotated
            if canonical not in seen:
                seen.add(canonical)
                necklaces.append(canonical)
    return sorted(necklaces)


def check_bad_sccs(state_counts, cycle, movers):
    """Check for bad SCCs in the forced-move graph.
    Returns (has_bad_sccs, n_bad_scc_configs, n_sccs).
    """
    n = len(state_counts)
    total = prod(state_counts)

    # Build determined entries from cycle
    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        mover = movers[idx]
        L = c[(mover - 1) % n]; S = c[mover]; R = c[(mover + 1) % n]
        det[(mover, L, S, R)] = c_next[mover]
        for i in range(n):
            if i != mover:
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                det[(i, L, S, R)] = S

    good_set = set(cycle)

    # Build forced-successor graph among non-good configs
    all_configs = list(cartesian(*(range(m) for m in state_counts)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    forced_succs = {}
    for c in non_good:
        succs = []
        for i in range(n):
            L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
            key = (i, L, S, R)
            if key in det and det[key] != S:
                new_c = list(c)
                new_c[i] = det[key]
                new_c = tuple(new_c)
                if new_c in non_good_set:
                    succs.append(new_c)
        if succs:
            forced_succs[c] = succs

    # Iterative Tarjan SCC
    index_counter = [0]
    stack = []
    on_stack = set()
    index_map = {}
    lowlink = {}
    sccs = []

    def strongconnect_iter(v):
        work = [(v, 0)]
        index_map[v] = lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)

        while work:
            node, si = work[-1]
            succs = forced_succs.get(node, [])
            if si < len(succs):
                work[-1] = (node, si + 1)
                w = succs[si]
                if w not in index_map:
                    index_map[w] = lowlink[w] = index_counter[0]
                    index_counter[0] += 1
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
                    if len(scc) > 1 or (len(scc) == 1 and node in forced_succs.get(node, [])):
                        sccs.append(scc)
                work.pop()
                if work:
                    parent = work[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[node])

    for v in forced_succs:
        if v not in index_map:
            strongconnect_iter(v)

    n_configs = sum(len(scc) for scc in sccs)
    return len(sccs) > 0, n_configs, len(sccs), sorted([len(s) for s in sccs], reverse=True)


def main():
    n = 9
    print("=" * 70)
    print(f"DFS PIPELINE TEST: product 8748 at n={n}")
    print("=" * 70)

    necklaces = necklaces_2binary(n)
    print(f"\n{len(necklaces)} necklaces to test")

    total_cycles = 0
    total_survivors = 0

    for ni, ms in enumerate(necklaces):
        ms_list = list(ms)
        bin_pos = [i for i in range(n) if ms[i] == 2]
        sep = min((bin_pos[1] - bin_pos[0]) % n, (bin_pos[0] - bin_pos[1]) % n)

        print(f"\n{'=' * 60}")
        print(f"[{ni+1}/{len(necklaces)}] ms={ms}, sep={sep}, product={prod(ms_list)}")
        print(f"{'=' * 60}")

        # Generate all orientations (rotations) of this necklace
        orientations = set()
        for rot in range(n):
            ori = tuple(ms[(k + rot) % n] for k in range(n))
            orientations.add(ori)
        orientations = sorted(orientations)
        print(f"  {len(orientations)} orientations")

        for oi, ori in enumerate(orientations):
            sc = tuple(ori)
            sc_str = ','.join(map(str, sc))
            t0 = time.time()

            # DFS search for good cycles
            n_screened = 0
            n_survived = 0
            scc_stats = []

            for cycle, movers_list in enumerate_good_cycles(
                sc, time_limit=15.0, max_cycles=500, max_depth=100
            ):
                n_screened += 1
                total_cycles += 1

                # Check for bad SCCs
                movers = list(movers_list) if not isinstance(movers_list, list) else movers_list
                has_bad, n_bad_configs, n_sccs, scc_sizes = check_bad_sccs(sc, cycle, movers)

                if not has_bad:
                    n_survived += 1
                    total_survivors += 1
                    print(f"    SURVIVOR! len={len(cycle)}, movers={movers[:20]}...")
                    scc_stats.append(('SURVIVOR', len(cycle), 0, []))
                else:
                    scc_stats.append(('DEAD', len(cycle), n_bad_configs, scc_sizes))

                if n_screened >= 200:
                    break

            elapsed = time.time() - t0

            if n_screened == 0:
                print(f"  [{oi+1}] ({sc_str}): NO CYCLES ({elapsed:.1f}s)")
            else:
                print(f"  [{oi+1}] ({sc_str}): screened={n_screened} survived={n_survived} ({elapsed:.1f}s)")
                if scc_stats and n_survived == 0:
                    # Show SCC stats for first few
                    unique_scc_patterns = Counter(tuple(s[3]) for s in scc_stats[:50])
                    for pat, count in unique_scc_patterns.most_common(5):
                        print(f"    SCC pattern {list(pat)}: {count} cycles")

    print(f"\n{'=' * 70}")
    print(f"SUMMARY: {total_cycles} cycles screened, {total_survivors} survivors")
    print(f"{'=' * 70}")

    if total_survivors > 0:
        print("*** SURVIVORS FOUND — potential witnesses at product 8748! ***")
    else:
        print("All cycles at product 8748 have bad SCCs. Screening wall holds.")
        print("\nThis suggests M_9 > 8748 for the standard pipeline.")
        print("But non-standard approaches (CEGAR, random search) might find witnesses.")


if __name__ == "__main__":
    main()
