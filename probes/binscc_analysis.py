#!/usr/bin/env python3
"""binscc_analysis.py — Binary subspace SCC obstruction analysis.

For architectures with ≥3 binary processors, analyze the {0,1}^n subspace
for forced SCCs that cannot be broken by any completion of free entries.

Key idea: A good cycle determines transition entries. In the binary subspace
{0,1}^n, binary processors (m=2) have ALL contexts (L,S,R) with L,S,R ∈ {0,1},
so their entries are heavily determined. If forced edges in {0,1}^n form SCCs,
no completion can achieve convergence.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
import time


# ============================================================
# Core helpers
# ============================================================

def build_bounce_cycle(ms, n, base_pattern=None, max_reps=5):
    """Build a bounce cycle for given state counts."""
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
    """Extract determined entries from a good cycle."""
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
    """Tarjan's SCC algorithm (iterative)."""
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
    """Analyze the {0,1}^n subspace for forced SCCs.

    Returns dict with:
      binary_configs: total configs in {0,1}^n
      binary_nongood: configs in {0,1}^n \ good_set
      determined_count: how many binary-context entries are determined
      total_binary_entries: total possible binary-context entries
      forced_edges: number of forced edges within binary non-good subspace
      sccs: list of SCC sizes
      trapped: total configs in SCCs
      scc_details: list of dicts with SCC analysis
    """
    # Generate binary subspace
    binary_configs = list(cartesian(*([range(2)] * n)))
    binary_set = set(binary_configs)
    binary_nongood = [c for c in binary_configs if c not in good_set]
    binary_nongood_set = set(binary_nongood)
    binary_good = [c for c in binary_configs if c in good_set]

    # Count determined entries in binary contexts
    determined_binary = 0
    total_binary_entries = 0
    for p in range(n):
        for L in range(2):
            for S in range(2):
                for R in range(2):
                    total_binary_entries += 1
                    if (p, L, S, R) in det:
                        determined_binary += 1

    # Build forced-edge graph on binary non-good configs
    forced_adj = defaultdict(list)
    for c in binary_nongood:
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if key in det and det[key] != S:
                out = det[key]
                # Check if output keeps us in binary subspace
                if out <= 1:
                    new_c = list(c)
                    new_c[p] = out
                    new_c = tuple(new_c)
                    if new_c in binary_nongood_set:
                        forced_adj[c].append(new_c)

    # Find SCCs
    sccs = find_sccs(dict(forced_adj))
    trapped = sum(len(s) for s in sccs)
    scc_sizes = sorted([len(s) for s in sccs], reverse=True)

    # Analyze each SCC
    scc_details = []
    for scc in sccs:
        scc_set_local = set(scc)
        # Which processors fire inside the SCC?
        internal_movers = set()
        for c in scc:
            for p in range(n):
                L = c[(p-1) % n]
                S = c[p]
                R = c[(p+1) % n]
                key = (p, L, S, R)
                if key in det and det[key] != S:
                    new_c = list(c)
                    new_c[p] = det[key]
                    new_c = tuple(new_c)
                    if new_c in scc_set_local:
                        internal_movers.add(p)

        # Hamming weight distribution
        hamming_dist = defaultdict(int)
        for c in scc:
            hamming_dist[sum(c)] += 1

        scc_details.append({
            'size': len(scc),
            'internal_movers': sorted(internal_movers),
            'hamming_dist': dict(hamming_dist),
        })

    # Count forced edges
    total_forced = sum(len(v) for v in forced_adj.values())

    # Also count how many binary non-good configs have ALL processors determined
    fully_determined = 0
    for c in binary_nongood:
        all_det = True
        for p in range(n):
            L = c[(p-1) % n]
            S = c[p]
            R = c[(p+1) % n]
            if (p, L, S, R) not in det:
                all_det = False
                break
        if all_det:
            fully_determined += 1

    # Count configs with at least one forced move staying in binary subspace
    has_forced_binary_move = 0
    for c in binary_nongood:
        for p in range(n):
            L = c[(p-1) % n]
            S = c[p]
            R = c[(p+1) % n]
            key = (p, L, S, R)
            if key in det and det[key] != S and det[key] <= 1:
                has_forced_binary_move += 1
                break

    return {
        'binary_total': len(binary_configs),
        'binary_good': len(binary_good),
        'binary_nongood': len(binary_nongood),
        'determined_binary_entries': determined_binary,
        'total_binary_entries': total_binary_entries,
        'det_fraction': determined_binary / total_binary_entries if total_binary_entries > 0 else 0,
        'fully_determined_configs': fully_determined,
        'has_forced_binary_move': has_forced_binary_move,
        'forced_edges': total_forced,
        'scc_count': len(sccs),
        'scc_sizes': scc_sizes,
        'trapped': trapped,
        'scc_details': scc_details,
    }


def analyze_full_forced_sccs(ms, n, det, good_set):
    """Analyze forced SCCs across ALL non-good configs (not just binary subspace)."""
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
    scc_sizes = sorted([len(s) for s in sccs], reverse=True)

    # Check how many SCC configs are all-binary
    binary_in_sccs = 0
    for scc in sccs:
        for c in scc:
            if all(v <= 1 for v in c):
                binary_in_sccs += 1

    return {
        'total_configs': len(all_configs),
        'non_good': len(non_good),
        'scc_count': len(sccs),
        'scc_sizes': scc_sizes,
        'trapped': trapped,
        'binary_in_sccs': binary_in_sccs,
    }


# ============================================================
# Main analysis
# ============================================================

if __name__ == "__main__":
    # ---- Part 1: n=9 gap multisets ----
    n = 9

    gap_multisets = [
        (2,2,2,2,2,2,5,5,5),     # 8000
        (2,2,2,2,2,2,2,3,21),    # 8064
        (2,2,2,2,2,2,3,6,7),     # 8064
        (2,2,2,2,2,3,3,4,7),     # 8064
        (2,2,2,2,2,2,2,7,9),     # 8064
        (2,2,2,2,2,2,2,4,16),    # 8192
        (2,2,2,2,2,2,4,4,8),     # 8192
        (2,2,2,2,2,4,4,4,4),     # 8192
        (2,2,2,2,2,2,2,8,8),     # 8192
        (2,2,2,2,2,2,2,5,13),    # 8320
        (2,2,2,2,2,2,2,3,22),    # 8448
        (2,2,2,2,2,2,2,6,11),    # 8448
        (2,2,2,2,2,2,3,4,11),    # 8448
        (2,2,2,2,2,2,3,3,15),    # 8640
        (2,2,2,2,2,2,3,5,9),     # 8640
        (2,2,2,2,2,3,3,5,6),     # 8640
        (2,2,2,2,3,3,3,4,5),     # 8640
        (2,2,2,2,2,3,3,3,10),    # 8640
        (2,2,2,2,2,2,2,4,17),    # 8704
    ]

    # Also test above-8748 with ≥3 binary
    above_multisets = [
        (2,2,2,3,3,3,3,3,5),     # 9720
        (2,2,2,3,3,3,3,3,3),     # 5832 (actually < 7776 but 3 binary)
        (2,2,2,2,3,3,3,3,3),     # 3888
    ]

    # The working witness for comparison (only 2 binary)
    witness_ms = (2,3,3,3,3,3,3,3,2)  # 8748, VALID

    bounce_patterns = {
        'up-down': lambda n: list(range(n)) + list(range(n-2, 0, -1)),
        'down-up': lambda n: list(range(n-1, -1, -1)) + list(range(1, n)),
    }

    print("=" * 78)
    print("BINARY SUBSPACE SCC ANALYSIS — n=9, ≥3 binary processors")
    print("=" * 78)
    print(f"\nBinary subspace: {{0,1}}^{n} = {2**n} configs\n")

    # First: analyze the VALID witness (2 binary) as baseline
    print("-" * 78)
    print("BASELINE: Valid witness ms=(2,3,3,3,3,3,3,3,2) [2 binary, product=8748]")
    print("-" * 78)

    bp = bounce_patterns['up-down'](n)
    cycle, movers = build_bounce_cycle(witness_ms, n, bp)
    if cycle:
        det = extract_determined(cycle, movers, n)
        good_set = set(cycle)
        result = analyze_binary_subspace(witness_ms, n, det, good_set)
        print(f"  Cycle length: {len(cycle)}")
        print(f"  Binary good: {result['binary_good']}/{result['binary_total']}")
        print(f"  Binary non-good: {result['binary_nongood']}")
        print(f"  Determined binary entries: {result['determined_binary_entries']}/{result['total_binary_entries']} "
              f"({result['det_fraction']:.1%})")
        print(f"  Fully-determined binary configs: {result['fully_determined_configs']}")
        print(f"  Forced edges in binary subspace: {result['forced_edges']}")
        print(f"  Binary SCCs: {result['scc_count']}, trapped: {result['trapped']}")
        if result['scc_sizes']:
            print(f"  SCC sizes: {result['scc_sizes'][:10]}")
        print()

    # Now: analyze gap multisets
    print("=" * 78)
    print("GAP MULTISETS (product 8000-8704, all ≥3 binary)")
    print("=" * 78)

    results_table = []

    for ms_sorted in gap_multisets:
        product_val = 1
        for m in ms_sorted:
            product_val *= m
        n_binary = sum(1 for m in ms_sorted if m == 2)

        # Try the sorted order directly (binaries at front)
        ms = ms_sorted

        best_result = None
        best_pattern = None

        for pname, pfunc in bounce_patterns.items():
            bp = pfunc(n)
            cycle, movers = build_bounce_cycle(ms, n, bp)
            if cycle is None:
                continue

            det = extract_determined(cycle, movers, n)
            good_set = set(cycle)
            result = analyze_binary_subspace(ms, n, det, good_set)
            result['cycle_len'] = len(cycle)
            result['pattern'] = pname

            if best_result is None or result['trapped'] > best_result['trapped']:
                best_result = result
                best_pattern = pname

        if best_result is None:
            print(f"  {ms} prod={product_val} ({n_binary}B): NO BOUNCE CYCLE")
            continue

        r = best_result
        status = "SCC!" if r['trapped'] > 0 else "no SCC"
        print(f"  {ms} prod={product_val} ({n_binary}B, {best_pattern}): "
              f"cyc={r['cycle_len']}, det={r['det_fraction']:.0%}, "
              f"SCCs={r['scc_count']}, trapped={r['trapped']}/{r['binary_nongood']} [{status}]")
        if r['scc_sizes']:
            print(f"    SCC sizes: {r['scc_sizes'][:10]}")
            for i, d in enumerate(r['scc_details'][:3]):
                print(f"    SCC[{i}]: movers={d['internal_movers']}, "
                      f"hamming={dict(sorted(d['hamming_dist'].items()))}")

        results_table.append((ms, product_val, n_binary, best_result))

    # Above-8748 multisets
    print(f"\n{'=' * 78}")
    print("ABOVE-8748 MULTISETS (≥3 binary)")
    print("=" * 78)

    for ms_sorted in above_multisets:
        product_val = 1
        for m in ms_sorted:
            product_val *= m
        n_binary = sum(1 for m in ms_sorted if m == 2)
        ms = ms_sorted

        for pname, pfunc in bounce_patterns.items():
            bp = pfunc(n)
            cycle, movers = build_bounce_cycle(ms, n, bp)
            if cycle is None:
                continue

            det = extract_determined(cycle, movers, n)
            good_set = set(cycle)
            r = analyze_binary_subspace(ms, n, det, good_set)
            r['cycle_len'] = len(cycle)

            status = "SCC!" if r['trapped'] > 0 else "no SCC"
            print(f"  {ms} prod={product_val} ({n_binary}B, {pname}): "
                  f"cyc={r['cycle_len']}, det={r['det_fraction']:.0%}, "
                  f"SCCs={r['scc_count']}, trapped={r['trapped']}/{r['binary_nongood']} [{status}]")
            if r['scc_sizes']:
                print(f"    SCC sizes: {r['scc_sizes'][:10]}")

    # ---- Part 2: Cycle-independence test ----
    print(f"\n{'=' * 78}")
    print("CYCLE-INDEPENDENCE TEST")
    print("=" * 78)
    print("Testing whether binary SCCs persist across different mover patterns")

    # Pick a representative 3-binary architecture
    test_ms_list = [
        (2,2,2,3,3,3,3,3,5),   # above 8748
        (2,2,2,2,3,3,3,4,5),   # 8640
        (2,2,2,2,2,2,5,5,5),   # 8000
    ]

    alt_patterns = {
        'up-down': lambda n: list(range(n)) + list(range(n-2, 0, -1)),
        'down-up': lambda n: list(range(n-1, -1, -1)) + list(range(1, n)),
        'zigzag-A': lambda n: [0,1,0,2,1,3,2,4,3,5,4,6,5,7,6,8,7][:2*n-1] if n==9 else list(range(n)),
        'odds-evens': lambda n: [i for i in range(0,n,2)] + [i for i in range(n-1 if n%2==0 else n-2, -1, -2)],
    }

    for test_ms in test_ms_list:
        product_val = 1
        for m in test_ms:
            product_val *= m
        n_binary = sum(1 for m in test_ms if m == 2)

        print(f"\n  Architecture: {test_ms} (prod={product_val}, {n_binary}B)")

        for pname, pfunc in alt_patterns.items():
            bp = pfunc(n)
            cycle, movers = build_bounce_cycle(test_ms, n, bp)
            if cycle is None:
                print(f"    {pname}: no cycle")
                continue

            det = extract_determined(cycle, movers, n)
            good_set = set(cycle)
            r = analyze_binary_subspace(test_ms, n, det, good_set)

            full_r = analyze_full_forced_sccs(test_ms, n, det, good_set)

            print(f"    {pname}: cyc={len(cycle)}, "
                  f"bin_SCCs={r['scc_count']}(trapped={r['trapped']}), "
                  f"full_SCCs={full_r['scc_count']}(trapped={full_r['trapped']}, "
                  f"binary_in={full_r['binary_in_sccs']})")

    # ---- Part 3: n-dependence ----
    print(f"\n{'=' * 78}")
    print("N-DEPENDENCE TEST")
    print("=" * 78)

    for test_n in [5, 6, 7, 8, 9, 10, 11]:
        # Architecture: 3 binary at start, rest ternary
        ms_3b = tuple([2]*3 + [3]*(test_n - 3))
        product_val = 8 * (3**(test_n-3))
        n_binary = 3

        bp = list(range(test_n)) + list(range(test_n-2, 0, -1))
        cycle, movers = build_bounce_cycle(ms_3b, test_n, bp)

        if cycle is None:
            print(f"  n={test_n}: {ms_3b} prod={product_val} — no bounce cycle")
            continue

        det = extract_determined(cycle, movers, test_n)
        good_set = set(cycle)
        r = analyze_binary_subspace(ms_3b, test_n, det, good_set)

        print(f"  n={test_n}: {ms_3b} prod={product_val}, cyc={len(cycle)}, "
              f"bin={r['binary_total']}, nongood={r['binary_nongood']}, "
              f"det={r['det_fraction']:.0%}, SCCs={r['scc_count']}, "
              f"trapped={r['trapped']}")
        if r['scc_sizes']:
            print(f"    SCC sizes: {r['scc_sizes'][:10]}")

    # Also test 4-binary architectures across n
    print(f"\n  --- 4 binary + rest ternary ---")
    for test_n in [5, 6, 7, 8, 9, 10, 11]:
        if test_n < 5:
            continue
        ms_4b = tuple([2]*4 + [3]*(test_n - 4))
        product_val = 16 * (3**(test_n-4))

        bp = list(range(test_n)) + list(range(test_n-2, 0, -1))
        cycle, movers = build_bounce_cycle(ms_4b, test_n, bp)

        if cycle is None:
            print(f"  n={test_n}: {ms_4b} — no bounce cycle")
            continue

        det = extract_determined(cycle, movers, test_n)
        good_set = set(cycle)
        r = analyze_binary_subspace(ms_4b, test_n, det, good_set)

        print(f"  n={test_n}: {ms_4b} prod={product_val}, cyc={len(cycle)}, "
              f"bin={r['binary_total']}, nongood={r['binary_nongood']}, "
              f"det={r['det_fraction']:.0%}, SCCs={r['scc_count']}, "
              f"trapped={r['trapped']}")
        if r['scc_sizes']:
            print(f"    SCC sizes: {r['scc_sizes'][:10]}")

    # ---- Part 4: Compare ≤2 binary vs ≥3 binary ----
    print(f"\n{'=' * 78}")
    print("BINARY COUNT THRESHOLD")
    print("=" * 78)
    print("Comparing binary SCC presence by binary processor count at n=9\n")

    for nb in [1, 2, 3, 4, 5, 6, 7, 8, 9]:
        if nb > n:
            break
        ms_test = tuple([2]*nb + [3]*(n - nb))
        product_val = (2**nb) * (3**(n-nb))

        bp = list(range(n)) + list(range(n-2, 0, -1))
        cycle, movers = build_bounce_cycle(ms_test, n, bp)

        if cycle is None:
            print(f"  {nb}B: {ms_test} prod={product_val} — no bounce cycle")
            continue

        det = extract_determined(cycle, movers, n)
        good_set = set(cycle)
        r = analyze_binary_subspace(ms_test, n, det, good_set)

        marker = " ***" if r['scc_count'] > 0 else ""
        print(f"  {nb}B: {ms_test} prod={product_val}, cyc={len(cycle)}, "
              f"det={r['det_fraction']:.0%}, SCCs={r['scc_count']}, "
              f"trapped={r['trapped']}/{r['binary_nongood']}{marker}")

    print(f"\n{'=' * 78}")
    print("ANALYSIS COMPLETE")
    print("=" * 78)
