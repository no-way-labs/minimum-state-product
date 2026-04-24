#!/usr/bin/env python3
"""alt_arch_n9_search.py — Test alternative product-7776 architectures at n=9.

Everyone has been searching {2,2,2,3,3,3,3,3,4} (single quaternary).
All 56 necklaces are DEAD (zero survivors).

This script tests two alternative multisets with the same product 7776:
  A: {2,2,2,2,3,3,3,3,6} — 4 binary + 4 ternary + 1 six-state
  B: {2,2,2,2,2,3,3,3,9} — 5 binary + 3 ternary + 1 nine-state

NOTE: The user's suggested B orientations (2,3,2,3,2,9,3,3,2) and
(9,2,3,2,3,2,3,3,2) actually have multiset {2^4, 3^4, 9}, product 11664.
We correct these to proper {2^5, 3^3, 9} orientations below.
"""

import sys
import os
import time
from itertools import product as cartesian, permutations
from collections import Counter

sys.path.insert(0, os.path.dirname(__file__))

from p2_good_cycle_search import enumerate_good_cycles, search_good_cycle, local_context
from p2_completion_search import has_fatal_forced_cycle_singletons
from p2_cycle_screen import forced_rule_map
from p2_ring import build_dijkstra_solution_3, verify_system
from p2_smt_completion import solve_cycle_with_smt


def prod(sc):
    p = 1
    for m in sc:
        p *= m
    return p


def max_consec(sc, val):
    """Max consecutive run of val in circular tuple."""
    n = len(sc)
    d = list(sc) * 2
    mx = cur = 0
    for i in range(2 * n):
        if d[i] == val:
            cur += 1
            mx = max(mx, cur)
        else:
            cur = 0
    return min(mx, n)


def necklaces_for_multiset(ms_counter, n):
    """All necklaces (up to rotation) for a multiset on n positions."""
    items = []
    for v in sorted(ms_counter):
        items.extend([v] * ms_counter[v])
    seen = set()
    out = []
    for p in set(permutations(items)):
        c = min(p[i:] + p[:i] for i in range(n))
        if c not in seen:
            seen.add(c)
            out.append(c)
    return sorted(out)


def quick_probe(sc, timeout=10.0):
    """Check if any good cycle exists from all-zeros."""
    result = search_good_cycle(sc, time_limit=timeout)
    return result.cycle is not None, result


def full_pipeline(sc, screen_time=120.0, max_cycles=10000, max_survivors=20,
                  smt_timeout_ms=60000):
    """Enumerate good cycles -> screen -> SMT complete."""
    t0 = time.time()
    screened = survivors = 0

    for cycle, movers in enumerate_good_cycles(
        sc, time_limit=screen_time, max_cycles=max_cycles
    ):
        screened += 1
        if screened % 2000 == 0:
            print(f"      ...screened {screened} ({time.time()-t0:.0f}s)")

        cycle_set = frozenset(cycle)
        try:
            fm = forced_rule_map(cycle, movers)
        except ValueError:
            continue

        if has_fatal_forced_cycle_singletons(sc, cycle_set, fm):
            continue

        survivors += 1
        print(f"      survivor {survivors}: len={len(cycle)} movers={movers}")

        result = solve_cycle_with_smt(sc, cycle, movers, timeout_ms=smt_timeout_ms)
        print(f"        SMT: {result.message} ({result.elapsed:.1f}s)")

        if result.found and result.system is not None:
            return result.system, screened, survivors, time.time() - t0

        if survivors >= max_survivors:
            break

    return None, screened, survivors, time.time() - t0


def print_witness(system):
    v = verify_system(system)
    print(f"  Verification: {v.message}")
    for cs in v.cycle_summaries:
        print(f"  Cycle length: {cs.length}")
    print(f"  State counts: {system.state_counts}")
    print(f"  Product: {system.size}")
    for i, table in enumerate(system.rules):
        priv = [(ctx, out) for ctx, out in sorted(table.items()) if out != ctx[1]]
        print(f"  P{i} (m={system.state_counts[i]}): "
              f"{len(priv)} privileged / {len(table)} total")
        for ctx, out in priv:
            print(f"    f{ctx} = {out}")


def main():
    results = []

    # ── Phase 0: Sanity check ──
    print("=" * 70)
    print("PHASE 0: Dijkstra Solution 3, n=9 (sanity check)")
    print("=" * 70)
    t0 = time.time()
    system = build_dijkstra_solution_3(9)
    result = verify_system(system)
    elapsed = time.time() - t0
    print(f"  Product={system.size}, "
          f"{'PASS' if result.valid else 'FAIL'}: {result.message}")
    if result.valid:
        for cs in result.cycle_summaries:
            print(f"  Good cycle length: {cs.length}")
    print(f"  Time: {elapsed:.2f}s")

    if not result.valid:
        print("SANITY CHECK FAILED. Aborting.")
        return

    # ── Phase 1: Quick probes ──
    print(f"\n{'=' * 70}")
    print("PHASE 1: Quick probes (10s) — check good-cycle existence")
    print("=" * 70)

    # Multiset A: {2^4, 3^4, 6^1}, product = 16*81*6 = 7776
    targets_a = [
        ("A1", (2, 3, 2, 3, 6, 3, 2, 3, 2)),
        ("A2", (2, 2, 3, 6, 3, 3, 2, 3, 2)),
        ("A3", (6, 2, 3, 2, 3, 2, 3, 3, 2)),
        ("A4", (2, 3, 6, 3, 2, 3, 2, 3, 2)),
        ("A5", (2, 6, 3, 2, 3, 2, 3, 3, 2)),
    ]
    # Multiset B: {2^5, 3^3, 9^1}, product = 32*27*9 = 7776
    targets_b = [
        ("B1", (2, 3, 2, 3, 2, 9, 2, 3, 2)),
        ("B2", (9, 2, 3, 2, 2, 3, 2, 3, 2)),
        ("B3", (2, 2, 3, 9, 2, 3, 2, 3, 2)),
    ]
    # User's exact suggested orientations — these are {2^4, 3^4, 9}, product 11664
    # Still valid upper bound candidates (better than Dijkstra's 19683)
    targets_user = [
        ("U1", (2, 3, 2, 3, 2, 9, 3, 3, 2)),  # product 11664
        ("U2", (9, 2, 3, 2, 3, 2, 3, 3, 2)),  # product 11664
    ]

    all_targets = targets_a + targets_b
    all_targets_with_user = all_targets + targets_user
    probe_results = {}

    for name, sc in all_targets_with_user:
        mc = max_consec(sc, 2)
        p = prod(sc)
        expected = 7776 if name.startswith(('A', 'B')) else 11664
        assert p == expected, f"{name}: product {p} != {expected}"
        ms = Counter(sc)
        print(f"\n  {name}: ({','.join(map(str, sc))}) "
              f"multiset={dict(ms)} product={p} max_consec_bin={mc}")
        found, result = quick_probe(sc, timeout=10.0)
        probe_results[name] = found
        if found:
            print(f"    FOUND: length={len(result.cycle)}, "
                  f"{result.stats.nodes} nodes, {result.elapsed:.1f}s")
        else:
            print(f"    NONE:  {result.message} "
                  f"({result.stats.nodes} nodes, {result.elapsed:.1f}s)")

    # ── Phase 2: Full pipeline ──
    print(f"\n{'=' * 70}")
    print("PHASE 2: Full pipeline (120s) on live orientations")
    print("=" * 70)

    live = [(n, sc) for n, sc in all_targets_with_user
            if probe_results.get(n, False)]

    if not live:
        print("  No probes found cycles in 10s. Trying all with 60s...")
        for name, sc in all_targets_with_user:
            found, result = quick_probe(sc, timeout=60.0)
            if found:
                live.append((name, sc))
                print(f"    {name}: FOUND (length={len(result.cycle)})")

    if not live:
        print("  Still no good cycles found for any targeted orientation.")
    else:
        for name, sc in live:
            print(f"\n  --- {name}: ({','.join(map(str, sc))}) ---")
            witness, screened, survivors, elapsed = full_pipeline(sc)
            found = witness is not None
            status = ("WITNESS!" if found
                      else "DEAD (no survivors)" if survivors == 0
                      else f"{survivors} survivors, no completion")
            print(f"    Pipeline: screened={screened} survivors={survivors} "
                  f"-> {status} ({elapsed:.1f}s)")
            results.append((name, sc, screened, survivors, found))

            if witness:
                print(f"\n  *** WITNESS FOUND: {name} ***")
                print_witness(witness)
                return

    # ── Phase 3: Broader sweep ──
    print(f"\n{'=' * 70}")
    print("PHASE 3: Broader necklace sweep (60s per orientation)")
    print("=" * 70)

    tested = {t[1] for _, t in all_targets}

    for ms_counter, ms_name in [
        (Counter({2: 4, 3: 4, 6: 1}), "A: {2^4, 3^4, 6}"),
        (Counter({2: 5, 3: 3, 9: 1}), "B: {2^5, 3^3, 9}"),
    ]:
        print(f"\n  {ms_name}")
        t_neck = time.time()
        all_n = necklaces_for_multiset(ms_counter, 9)
        filtered = [n for n in all_n if max_consec(n, 2) <= 3]
        remaining = [n for n in filtered if n not in tested]
        print(f"  Necklaces: {len(all_n)} total, {len(filtered)} filtered "
              f"(<=3 consec bin), {len(remaining)} untested "
              f"({time.time()-t_neck:.1f}s)")

        tested_count = 0
        for sc in remaining:
            if tested_count >= 15:
                print(f"    ... stopping after 15 orientations")
                break
            tested_count += 1

            sc_str = ','.join(map(str, sc))
            print(f"\n    [{tested_count}] ({sc_str})")

            found, result = quick_probe(sc, timeout=5.0)
            if not found:
                print(f"      No cycle ({result.stats.nodes} nodes, "
                      f"{result.elapsed:.1f}s)")
                results.append(("sweep", sc, 0, 0, False))
                continue

            print(f"      Cycle found (len={len(result.cycle)})")
            witness, screened, survivors, elapsed = full_pipeline(
                sc, screen_time=60.0, max_survivors=10
            )
            found = witness is not None
            status = ("WITNESS!" if found
                      else "DEAD" if survivors == 0
                      else f"{survivors} surv")
            print(f"      Pipeline: scr={screened} surv={survivors} "
                  f"-> {status} ({elapsed:.1f}s)")
            results.append(("sweep", sc, screened, survivors, found))

            if witness:
                print(f"\n  *** WITNESS FOUND ***")
                print_witness(witness)
                return

    # ── Summary ──
    print(f"\n{'=' * 70}")
    print("SUMMARY")
    print("=" * 70)
    for name, sc, screened, survivors, found in results:
        sc_str = ','.join(map(str, sc))
        marker = "WITNESS" if found else "DEAD"
        print(f"  {marker}: ({sc_str}) scr={screened} surv={survivors}")

    any_found = any(f for _, _, _, _, f in results)
    if not any_found:
        print("\n  No witnesses found for any alternative architecture.")
        print("  This may indicate product 7776 is not achievable at n=9,")
        print("  or that longer search / different methods are needed.")


if __name__ == "__main__":
    main()
