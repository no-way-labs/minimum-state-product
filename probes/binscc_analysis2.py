#!/usr/bin/env python3
"""binscc_analysis2.py — Binary SCC analysis with orientation search.

Key fix from v1: try many different orientations (permutations) of processors
around the ring, not just sorted order. Binary processors at consecutive
positions often prevent bounce cycles from closing.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian, permutations
from collections import defaultdict
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
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = S
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


def analyze_binary_subspace(ms, n, det, good_set):
    binary_configs = list(cartesian(*([range(2)] * n)))
    binary_nongood = [c for c in binary_configs if c not in good_set]
    binary_nongood_set = set(binary_nongood)
    binary_good = [c for c in binary_configs if c in good_set]

    det_count = 0
    total_count = 0
    for p in range(n):
        for L in range(2):
            for S in range(2):
                for R in range(2):
                    total_count += 1
                    if (p, L, S, R) in det:
                        det_count += 1

    # Build forced-edge graph on binary non-good configs
    forced_adj = defaultdict(list)
    for c in binary_nongood:
        for p in range(n):
            L = c[(p-1) % n]
            S = c[p]
            R = c[(p+1) % n]
            key = (p, L, S, R)
            if key in det and det[key] != S:
                out = det[key]
                if out <= 1:  # stays in binary subspace
                    new_c = list(c)
                    new_c[p] = out
                    new_c = tuple(new_c)
                    if new_c in binary_nongood_set:
                        forced_adj[c].append(new_c)

    sccs = find_sccs(dict(forced_adj))
    trapped = sum(len(s) for s in sccs)
    scc_sizes = sorted([len(s) for s in sccs], reverse=True)

    # Analyze internal movers per SCC
    scc_details = []
    for scc in sccs[:5]:
        scc_set_local = set(scc)
        internal_movers = set()
        for c in scc:
            for p in range(n):
                L = c[(p-1) % n]
                S = c[p]
                R = c[(p+1) % n]
                key = (p, L, S, R)
                if key in det and det[key] != S and det[key] <= 1:
                    new_c = list(c)
                    new_c[p] = det[key]
                    if tuple(new_c) in scc_set_local:
                        internal_movers.add(p)
        scc_details.append({'size': len(scc), 'movers': sorted(internal_movers)})

    return {
        'binary_total': 2**n,
        'binary_good': len(binary_good),
        'binary_nongood': len(binary_nongood),
        'det_count': det_count,
        'det_total': total_count,
        'det_frac': det_count / total_count if total_count else 0,
        'forced_edges': sum(len(v) for v in forced_adj.values()),
        'scc_count': len(sccs),
        'scc_sizes': scc_sizes,
        'trapped': trapped,
        'scc_details': scc_details,
    }


def generate_orientations(ms_sorted, n, max_orient=50):
    """Generate distinct orientations of a multiset around the ring."""
    seen = set()
    orientations = []

    # Try sorted, reversed, and random shuffles
    candidates = [ms_sorted, tuple(reversed(ms_sorted))]

    # Spread binaries out: place them at even positions
    vals = sorted(ms_sorted)
    binaries = [v for v in vals if v == 2]
    nonbinaries = [v for v in vals if v != 2]
    nb = len(binaries)

    # Spread binaries evenly
    if 0 < nb < n:
        spread = [0] * n
        positions = [int(i * n / nb) % n for i in range(nb)]
        remaining = [i for i in range(n) if i not in positions]
        perm = [0] * n
        for i, pos in enumerate(positions):
            perm[pos] = 2
        ni = 0
        for pos in remaining:
            if ni < len(nonbinaries):
                perm[pos] = nonbinaries[ni]
                ni += 1
        candidates.append(tuple(perm))

        # Binaries at endpoints and middle
        if nb >= 3:
            perm2 = list(nonbinaries) + [2]*nb
            # Put binaries at 0, n//2, n-1
            perm3 = [0]*n
            bin_pos = [0, n//2, n-1] + list(range(1, n-1))
            bi = 0
            nbi = 0
            for pos in range(n):
                if pos in [0, n//2, n-1] and bi < nb:
                    perm3[pos] = 2
                    bi += 1
                else:
                    if nbi < len(nonbinaries):
                        perm3[pos] = nonbinaries[nbi]
                        nbi += 1
                    else:
                        perm3[pos] = 2
                        bi += 1
            candidates.append(tuple(perm3))

    # Random shuffles
    for _ in range(max_orient):
        perm = list(ms_sorted)
        random.shuffle(perm)
        candidates.append(tuple(perm))

    for c in candidates:
        if c not in seen:
            seen.add(c)
            orientations.append(c)

    return orientations


if __name__ == "__main__":
    n = 9

    gap_multisets = [
        (2,2,2,2,2,2,5,5,5),
        (2,2,2,2,2,2,3,6,7),
        (2,2,2,2,2,3,3,4,7),
        (2,2,2,2,2,2,4,4,8),
        (2,2,2,2,2,4,4,4,4),
        (2,2,2,2,2,2,3,3,15),
        (2,2,2,2,2,2,3,5,9),
        (2,2,2,2,2,3,3,5,6),
        (2,2,2,2,3,3,3,4,5),
        (2,2,2,2,2,3,3,3,10),
    ]

    # Also above-8748 with >=3 binary
    extra_multisets = [
        (2,2,2,3,3,3,3,3,5),     # 9720
        (2,2,2,3,3,3,3,3,3),     # 5832
        (2,2,2,2,3,3,3,3,3),     # 3888
    ]

    bounce_patterns = [
        ('up-down', lambda n: list(range(n)) + list(range(n-2, 0, -1))),
        ('down-up', lambda n: list(range(n-1, -1, -1)) + list(range(1, n))),
    ]

    print("=" * 78)
    print("BINARY SCC ANALYSIS v2 — n=9, orientation search")
    print("=" * 78)

    # ---- Baseline ----
    print("\nBASELINE: ms=(2,3,3,3,3,3,3,3,2), 2 binary at endpoints")
    ms = (2,3,3,3,3,3,3,3,2)
    bp = list(range(n)) + list(range(n-2, 0, -1))
    cycle, movers = build_bounce_cycle(ms, n, bp)
    det = extract_determined(cycle, movers, n)
    good_set = set(cycle)
    r = analyze_binary_subspace(ms, n, det, good_set)
    print(f"  cyc={len(cycle)}, det={r['det_frac']:.0%}, "
          f"SCCs={r['scc_count']}, trapped={r['trapped']}/{r['binary_nongood']}")

    # ---- Gap multisets with orientation search ----
    print(f"\n{'=' * 78}")
    print("GAP & EXTRA MULTISETS — orientation search")
    print("=" * 78)

    all_results = {}

    for ms_sorted in gap_multisets + extra_multisets:
        product_val = 1
        for m in ms_sorted:
            product_val *= m
        nb = sum(1 for m in ms_sorted if m == 2)

        orientations = generate_orientations(ms_sorted, n, max_orient=80)

        best = None
        worst = None
        cycle_count = 0
        scc_always = True
        scc_never = True

        for orient in orientations:
            for pname, pfunc in bounce_patterns:
                bp = pfunc(n)
                cycle, movers = build_bounce_cycle(orient, n, bp)
                if cycle is None:
                    continue

                cycle_count += 1
                det = extract_determined(cycle, movers, n)
                good_set = set(cycle)
                r = analyze_binary_subspace(orient, n, det, good_set)
                r['orient'] = orient
                r['pattern'] = pname
                r['cycle_len'] = len(cycle)

                if r['scc_count'] > 0:
                    scc_never = False
                else:
                    scc_always = False

                if best is None or r['trapped'] > best['trapped']:
                    best = r
                if worst is None or r['trapped'] < worst['trapped']:
                    worst = r

        tag = f"{ms_sorted} prod={product_val} ({nb}B)"
        if cycle_count == 0:
            print(f"\n  {tag}: NO CYCLES found across {len(orientations)} orientations")
            continue

        print(f"\n  {tag}: {cycle_count} cycles from {len(orientations)} orientations")

        if scc_always:
            print(f"    *** SCCs in ALL {cycle_count} cycles ***")
        elif scc_never:
            print(f"    No SCCs in any cycle")
        else:
            print(f"    SCCs in SOME cycles")

        if best:
            print(f"    Best (most trapped): orient={best['orient']}, {best['pattern']}, "
                  f"cyc={best['cycle_len']}, SCCs={best['scc_count']}, "
                  f"trapped={best['trapped']}/{best['binary_nongood']}")
            if best['scc_sizes']:
                print(f"      SCC sizes: {best['scc_sizes'][:15]}")
        if worst and worst != best:
            print(f"    Worst (least trapped): orient={worst['orient']}, {worst['pattern']}, "
                  f"cyc={worst['cycle_len']}, SCCs={worst['scc_count']}, "
                  f"trapped={worst['trapped']}/{worst['binary_nongood']}")

        all_results[ms_sorted] = {
            'cycle_count': cycle_count,
            'scc_always': scc_always,
            'scc_never': scc_never,
            'best': best,
            'worst': worst,
        }

    # ---- Summary ----
    print(f"\n{'=' * 78}")
    print("SUMMARY")
    print("=" * 78)
    print(f"\n{'Multiset':<35} {'Prod':>6} {'#B':>3} {'Cycles':>6} {'SCC?':>10}")
    print("-" * 65)
    for ms_sorted in gap_multisets + extra_multisets:
        product_val = 1
        for m in ms_sorted:
            product_val *= m
        nb = sum(1 for m in ms_sorted if m == 2)
        if ms_sorted not in all_results:
            print(f"{str(ms_sorted):<35} {product_val:>6} {nb:>3} {'NONE':>6} {'N/A':>10}")
            continue
        ar = all_results[ms_sorted]
        scc_label = "ALWAYS" if ar['scc_always'] else ("NEVER" if ar['scc_never'] else "SOME")
        print(f"{str(ms_sorted):<35} {product_val:>6} {nb:>3} {ar['cycle_count']:>6} {scc_label:>10}")

    # ---- Binary threshold test ----
    print(f"\n{'=' * 78}")
    print("BINARY THRESHOLD — {2}^k + {3}^(9-k)")
    print("=" * 78)

    for nb in range(1, 10):
        ms_test = tuple([2]*nb + [3]*(9-nb))
        product_val = (2**nb) * (3**(9-nb))

        orientations = generate_orientations(ms_test, 9, max_orient=40)
        cycle_count = 0
        any_scc = False
        best_trapped = 0

        for orient in orientations:
            for pname, pfunc in bounce_patterns:
                bp = pfunc(9)
                cycle, movers = build_bounce_cycle(orient, 9, bp)
                if cycle is None:
                    continue
                cycle_count += 1
                det = extract_determined(cycle, movers, 9)
                good_set = set(cycle)
                r = analyze_binary_subspace(orient, 9, det, good_set)
                if r['scc_count'] > 0:
                    any_scc = True
                    best_trapped = max(best_trapped, r['trapped'])

        scc_str = f"YES(max_trapped={best_trapped})" if any_scc else "no"
        print(f"  {nb}B: {ms_test} prod={product_val}, {cycle_count} cycles, SCC: {scc_str}")

    # ---- n-dependence ----
    print(f"\n{'=' * 78}")
    print("N-DEPENDENCE — ms=(2,2,2,...,3,...,3) with 3 binary at spread positions")
    print("=" * 78)

    for test_n in [5, 6, 7, 8, 9, 10, 11, 12]:
        # Place 3 binaries spread out
        ms_list = [3] * test_n
        positions = [0, test_n // 2, test_n - 1]
        for pos in positions:
            ms_list[pos] = 2
        ms_test = tuple(ms_list)
        product_val = 1
        for m in ms_test:
            product_val *= m

        bp = list(range(test_n)) + list(range(test_n-2, 0, -1))
        cycle, movers = build_bounce_cycle(ms_test, test_n, bp)

        if cycle is None:
            # Try other pattern
            bp2 = list(range(test_n-1, -1, -1)) + list(range(1, test_n))
            cycle, movers = build_bounce_cycle(ms_test, test_n, bp2)

        if cycle is None:
            print(f"  n={test_n}: {ms_test} prod={product_val} — no cycle")
            continue

        det = extract_determined(cycle, movers, test_n)
        good_set = set(cycle)
        r = analyze_binary_subspace(ms_test, test_n, det, good_set)

        marker = " ***" if r['scc_count'] > 0 else ""
        print(f"  n={test_n}: {ms_test} prod={product_val}, cyc={len(cycle)}, "
              f"|bin|={r['binary_total']}, nongood={r['binary_nongood']}, "
              f"det={r['det_frac']:.0%}, SCCs={r['scc_count']}, "
              f"trapped={r['trapped']}{marker}")
        if r['scc_sizes']:
            print(f"    SCC sizes: {r['scc_sizes'][:10]}")

    print(f"\n{'=' * 78}")
    print("DONE")
    print("=" * 78)
