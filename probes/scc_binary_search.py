#!/usr/bin/env python3
"""scc_binary_search.py — Binary search for the SCC obstruction threshold at n=9.

Tests products between 8748 and 19683 to find where the bad SCC obstruction
breaks. Uses the "all ternary except k slots" family for clean comparison:
  3^9 = 19683 (Dijkstra Sol 3 — works)
  2·3^8 = 13122 (1 binary + 8 ternary)
  4·3^7 = 8748 (1 quaternary + 8 ternary, or 2 binary + 7 ternary — DEAD)

Also tests intermediate products with mixed state counts.
"""

import sys
import os
import time
from itertools import product as cartesian, combinations_with_replacement
from collections import Counter

sys.path.insert(0, os.path.dirname(__file__))

from p2_good_cycle_search import enumerate_good_cycles, search_good_cycle
from p2_ring import RingSystem, verify_system


def prod(sc):
    p = 1
    for m in sc:
        p *= m
    return p


def check_cycle_consistency(cycle_configs, n, ms):
    L = len(cycle_configs)
    required = {}
    for idx in range(L):
        c = cycle_configs[idx]
        c_next = cycle_configs[(idx + 1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, {}, "non-single mover"
        mover = diffs[0]
        Li = c[(mover - 1) % n]; Si = c[mover]; Ri = c[(mover + 1) % n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return False, {}, "conflict"
        required[key] = S_new
        for i in range(n):
            if i != mover:
                Li = c[(i - 1) % n]; Si = c[i]; Ri = c[(i + 1) % n]
                key = (i, Li, Si, Ri)
                if key in required and required[key] != Si:
                    return False, {}, "conflict"
                required[key] = Si
    return True, required, "OK"


def construct_sweep_cycle(ms, n, nb_vals):
    config = [0] * n
    cycle = [tuple(config)]
    for proc in range(n):
        config = list(cycle[-1])
        new_val = nb_vals.get(proc, 1) if ms[proc] > 2 else 1
        if ms[proc] == 2:
            new_val = 1
        if config[proc] == new_val:
            return None
        config[proc] = new_val
        cycle.append(tuple(config))
    for proc in range(n):
        config = list(cycle[-1])
        if config[proc] == 0:
            return None
        config[proc] = 0
        cycle.append(tuple(config))
    if cycle[-1] == cycle[0]:
        cycle = cycle[:-1]
    return cycle


def find_bad_sccs(det, good_set, ms, n):
    """Find bad SCCs via iterative Tarjan. Returns (n_configs_in_sccs, n_sccs, scc_sizes)."""
    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good_set = set(c for c in all_configs if c not in good_set)

    forced_succs = {}
    for c in non_good_set:
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

    # Iterative Tarjan
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

    scc_sizes = sorted([len(s) for s in sccs], reverse=True)
    total = sum(scc_sizes)
    return total, len(sccs), scc_sizes


def check_bad_sccs_from_cycle(state_counts, cycle, movers):
    """Check bad SCCs given a cycle and its movers."""
    n = len(state_counts)
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
    return find_bad_sccs(det, good_set, list(state_counts), n)


def enumerate_multisets_9(product_target):
    """Find all multisets of 9 integers ≥ 2 whose product = product_target."""
    n = 9
    results = []

    def backtrack(remaining_product, remaining_slots, min_val, current):
        if remaining_slots == 0:
            if remaining_product == 1:
                results.append(tuple(sorted(current)))
            return
        max_val = remaining_product  # upper bound
        for v in range(min_val, min(max_val + 1, remaining_product + 1)):
            if remaining_product % v == 0:
                # Check if remaining product / v can be made by (remaining_slots - 1) values ≥ v
                rp = remaining_product // v
                if rp >= v ** (remaining_slots - 1):
                    # Also check upper bound: rp ≤ max_single_val^(remaining_slots-1)
                    # (not strictly needed but helps prune)
                    backtrack(rp, remaining_slots - 1, v, current + [v])

    backtrack(product_target, n, 2, [])
    return sorted(set(results))


def necklaces_for_multiset(ms_tuple):
    """Generate all distinct necklaces (rotation equivalence classes) for a multiset."""
    from itertools import permutations
    n = len(ms_tuple)
    seen = set()
    necklaces = []
    # Generate all distinct permutations
    ms_list = list(ms_tuple)
    perms = set(permutations(ms_list))
    for perm in perms:
        canonical = min(tuple(perm[(k + rot) % n] for k in range(n)) for rot in range(n))
        if canonical not in seen:
            seen.add(canonical)
            necklaces.append(canonical)
    return sorted(necklaces)


def test_product(product_target, max_orientations=9, dfs_timeout=10.0, max_cycles=200, verbose=True):
    """Test all multisets at a given product. Returns summary dict."""
    n = 9

    if verbose:
        print(f"\n{'=' * 70}")
        print(f"TESTING PRODUCT {product_target}")
        print(f"{'=' * 70}")

    multisets = enumerate_multisets_9(product_target)
    if verbose:
        print(f"  Multisets found: {len(multisets)}")
        for ms in multisets:
            print(f"    {ms} = {dict(Counter(ms))}")

    total_cycles_screened = 0
    total_survivors = 0
    sweep_scc_summary = []
    dfs_scc_summary = []

    for ms in multisets:
        necklaces = necklaces_for_multiset(ms)
        if verbose:
            print(f"\n  Multiset {ms}: {len(necklaces)} necklaces")

        for neck in necklaces[:max_orientations]:
            ms_list = list(neck)

            # --- Uniform sweep SCC check ---
            nb_vals = {i: 1 for i in range(n)}
            cycle = construct_sweep_cycle(ms_list, n, nb_vals)
            if cycle:
                ok, det, msg = check_cycle_consistency(cycle, n, ms_list)
                if ok:
                    good_set = set(cycle)
                    t0 = time.time()
                    n_scc_configs, n_sccs, scc_sizes = find_bad_sccs(det, good_set, ms_list, n)
                    elapsed = time.time() - t0
                    sweep_scc_summary.append({
                        'ms': neck, 'n_sccs': n_sccs,
                        'n_scc_configs': n_scc_configs, 'scc_sizes': scc_sizes[:10],
                        'elapsed': elapsed
                    })
                    if verbose:
                        top = scc_sizes[:5] if scc_sizes else []
                        status = "CLEAN" if n_sccs == 0 else f"{n_sccs} SCCs"
                        print(f"    Sweep {neck}: {status}, {n_scc_configs} SCC configs, "
                              f"top={top} ({elapsed:.2f}s)")
                        if n_sccs == 0:
                            print(f"    *** SWEEP HAS NO BAD SCCs! ***")

            # --- DFS pipeline ---
            sc = tuple(neck)
            n_screened = 0
            n_survived = 0

            for cyc, movers_list in enumerate_good_cycles(
                sc, time_limit=dfs_timeout, max_cycles=max_cycles, max_depth=100
            ):
                n_screened += 1
                total_cycles_screened += 1
                movers = list(movers_list) if not isinstance(movers_list, list) else movers_list

                n_scc_c, n_sccs_c, scc_sizes_c = check_bad_sccs_from_cycle(sc, cyc, movers)

                if n_sccs_c == 0:
                    n_survived += 1
                    total_survivors += 1
                    if verbose:
                        print(f"    *** DFS SURVIVOR! len={len(cyc)} ***")

                dfs_scc_summary.append({
                    'ms': neck, 'cycle_len': len(cyc),
                    'n_sccs': n_sccs_c, 'n_scc_configs': n_scc_c,
                    'top_scc': scc_sizes_c[:3] if scc_sizes_c else []
                })

            if verbose and n_screened > 0:
                print(f"    DFS {neck}: screened={n_screened} survived={n_survived}")
            elif verbose and not cycle:
                print(f"    {neck}: no sweep cycle, ", end="")
                if n_screened == 0:
                    print("no DFS cycles")
                else:
                    print(f"DFS screened={n_screened} survived={n_survived}")

    summary = {
        'product': product_target,
        'n_multisets': len(multisets),
        'total_screened': total_cycles_screened,
        'total_survivors': total_survivors,
        'sweep_results': sweep_scc_summary,
        'has_clean_sweep': any(s['n_sccs'] == 0 for s in sweep_scc_summary),
    }

    if verbose:
        print(f"\n  PRODUCT {product_target} SUMMARY:")
        print(f"    Multisets: {len(multisets)}")
        print(f"    Total cycles screened: {total_cycles_screened}")
        print(f"    Total survivors: {total_survivors}")
        if summary['has_clean_sweep']:
            print(f"    *** HAS CLEAN SWEEP CYCLES (no bad SCCs)! ***")
        else:
            print(f"    All sweep cycles have bad SCCs")

    return summary


def main():
    print("=" * 70)
    print("SCC OBSTRUCTION BINARY SEARCH: n=9")
    print("Finding where the bad SCC obstruction breaks")
    print("Known: 8748 DEAD, 19683 ALIVE")
    print("=" * 70)

    # Step 1: Enumerate products in the "k-ary slot" family
    # These replace one or more ternary slots with higher state counts
    print("\n" + "─" * 60)
    print("STEP 1: PRODUCT FAMILY ENUMERATION")
    print("─" * 60)

    # The clean family: replace k ternary slots with other values
    # Base: 3^9 = 19683
    # Replace 1 slot of 3 with 2: 2·3^8 = 13122
    # Replace 2 slots of 3 with 2: 4·3^7 = 8748 (DEAD)
    # Replace 1 slot of 3 with 4: 4·3^8 = 26244 (above upper bound)
    # Replace 1 slot of 3 with 5: 5·3^8/3 = 5·3^7... no, 5·3^8 = 32805
    # Actually: 9 slots all ternary = 19683. Replace slot i's value:
    #   slot → 2: product × 2/3 = 13122
    #   slot → 4: product × 4/3 = 26244
    # So from 19683: going DOWN by replacing one 3 with 2 gives 13122.
    # From 13122: replacing another 3 with 2 gives 8748. DEAD.
    # From 19683: replacing one 3 with 2 gives 13122. THIS IS THE MIDPOINT.

    # Other interesting products in the gap:
    products_to_test = []

    # The "one slot different" family from 3^9
    # {2, 3^8} = 13122
    products_to_test.append((13122, "2·3^8"))

    # Other multisets in the gap
    # {2, 3^7, 4} = 2·4·3^7 / 3 ... no. {2, 3^7, 4} has product 2·4·3^7 = 17496
    # Wait: {2, 4, 3, 3, 3, 3, 3, 3, 3} = 2·4·3^7 = 17496
    products_to_test.append((17496, "2·4·3^7"))

    # {3^8, 4} = 4·3^8 = 26244 — above Dijkstra, skip
    # {2, 3^7, 5} = 2·5·3^7 = 21870 — above Dijkstra, skip

    # {3^7, 4, 4} = 16·3^7 = ... 16·2187 = 34992 — too high
    # Let me think differently. Multisets with product between 8748 and 19683:

    # Products where all entries ≥ 2:
    # 3^8 · 2 = 13122
    # 3^7 · 2 · 4 = 17496
    # 3^7 · 2 · 5 = 21870 (> 19683, skip)
    # 3^7 · 2 · 2 = 8748 (DEAD)
    # 3^8 · 2 = 13122
    # 3^6 · 2 · 4 · 3 = same as 3^7 · 2 · 4 = 17496
    # 3^7 · 4 = 8748 (DEAD — same product as 2·2·3^7)
    # Wait: {4, 3, 3, 3, 3, 3, 3, 3, 3} = 4·3^8 = 26244. No, 4·3^8 = 4·6561 = 26244.
    # {4, 3^7, 2} is a different multiset but same product as {2, 2, 3^7} only if
    # there are the right number of entries. Let me be careful.
    # n=9, so we need 9 entries.
    # {4, 3, 3, 3, 3, 3, 3, 3, 3} = 9 entries, product = 4 · 3^8 = 26244. Too high.
    # {2, 3, 3, 3, 3, 3, 3, 3, 3} = 9 entries, product = 2 · 3^8 = 13122. Good.
    # {2, 2, 3, 3, 3, 3, 3, 3, 3} = 9 entries, product = 4 · 3^7 = 8748. DEAD.
    # {2, 4, 3, 3, 3, 3, 3, 3, 3} = 9 entries, product = 8 · 3^7 = 17496.
    # {2, 2, 4, 3, 3, 3, 3, 3, 3} = 9 entries, product = 16 · 3^6 = 11664.
    # {2, 2, 2, 4, 3, 3, 3, 3, 3} = 9 entries, product = 32 · 3^5 = 7776. DEAD.
    # {2, 5, 3, 3, 3, 3, 3, 3, 3} = 9 entries, product = 10 · 3^7 = 21870. Too high.
    # {2, 2, 5, 3, 3, 3, 3, 3, 3} = 9 entries, product = 20 · 3^6 = 14580.

    products_to_test.append((11664, "2^2·4·3^6"))
    products_to_test.append((14580, "2^2·5·3^6"))

    # Also: {2, 2, 2, 3, 3, 3, 3, 3, 4} already tested at 7776 (DEAD)
    # {2, 2, 3, 3, 3, 3, 3, 3, 4} = 4·4·3^6... no.
    # Actually {2, 2, 3, 3, 3, 3, 3, 3, 4} = 2·2·4·3^5·3 ... let me just compute:
    # 2·2·4·3·3·3·3·3·3 = 2·2·4·3^6 = 16·729 = 11664. Same as above.

    # {2, 3, 3, 3, 3, 3, 3, 3, 4} = 2·4·3^7 = 8·2187 = 17496. Same as above.
    # {2, 3, 3, 3, 3, 3, 3, 4, 4} = 2·16·3^6 = 32·729 = 23328. Too high.

    # {3, 3, 3, 3, 3, 3, 3, 3, 4} = 4·3^8 = 26244. Too high.

    # So the relevant products are:
    # 8748 (DEAD), 11664, 13122, 14580, 17496, 19683 (ALIVE)

    products_to_test.sort(key=lambda x: x[0])

    print("\nProducts to test (in order):")
    print("  8748 = 4·3^7 — DEAD (Exploration 3)")
    for p, desc in products_to_test:
        print(f"  {p} = {desc}")
    print("  19683 = 3^9 — ALIVE (Dijkstra Sol 3)")

    # Step 2: Test each product
    print("\n" + "─" * 60)
    print("STEP 2: PRODUCT-BY-PRODUCT TESTING")
    print("─" * 60)

    results = {}
    # Start with midpoint
    for product_val, desc in products_to_test:
        print(f"\n{'#' * 60}")
        print(f"# PRODUCT {product_val} = {desc}")
        print(f"{'#' * 60}")

        summary = test_product(
            product_val,
            max_orientations=15,
            dfs_timeout=10.0,
            max_cycles=200,
            verbose=True
        )
        results[product_val] = summary

        if summary['total_survivors'] > 0:
            print(f"\n*** SURVIVORS FOUND AT PRODUCT {product_val}! ***")
            print(f"*** The SCC obstruction breaks at or before {product_val} ***")

    # Step 3: Summary
    print(f"\n{'=' * 70}")
    print("BINARY SEARCH SUMMARY")
    print(f"{'=' * 70}")
    print(f"\n{'Product':>8} {'Multisets':>10} {'Screened':>10} {'Survivors':>10} {'Clean Sweep':>12} {'Status':>8}")
    print("-" * 70)
    print(f"{'8748':>8} {'—':>10} {'628':>10} {'0':>10} {'No':>12} {'DEAD':>8}")
    for product_val, desc in products_to_test:
        s = results.get(product_val, {})
        clean = "Yes" if s.get('has_clean_sweep') else "No"
        status = "ALIVE?" if s.get('total_survivors', 0) > 0 else "DEAD"
        print(f"{product_val:>8} {s.get('n_multisets', '?'):>10} "
              f"{s.get('total_screened', '?'):>10} "
              f"{s.get('total_survivors', '?'):>10} {clean:>12} {status:>8}")
    print(f"{'19683':>8} {'—':>10} {'—':>10} {'—':>10} {'Yes':>12} {'ALIVE':>8}")


if __name__ == "__main__":
    main()
