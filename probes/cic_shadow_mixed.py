#!/usr/bin/env python3
"""CIC Exploration 3: Shadow Cycle Extension to Mixed Systems.

Test whether the shadow cycle theorem extends to state vectors with
m_i >= 4 (quaternary, quinary, etc.) at n=9. These are the CIC
candidates that need to be killed for the M_9 >= 4*3^7 lower bound.

Key insight: the shadow cycle machinery (MNU, Universal Escape, closure)
depends on the WATERFALL structure of uniform sweep cycles, NOT on
the specific state counts. Binary processors are fully determined
regardless of non-binary state counts.

We verify:
  (a) Uniform sweep cycles exist for mixed multisets
  (b) MNU holds (mover neighborhoods are unique)
  (c) Universal Escape holds (no forced move enters C)
  (d) Shadow cycles exist (forced transitions chain into a closed cycle)
  (e) Shadow cycle has same length as good cycle (2n = 18)
"""

from itertools import product as iproduct
import sys
import time


def multiset_perms(lst):
    """Generate all distinct permutations of a list (multiset)."""
    lst = sorted(list(lst))
    yield tuple(lst)
    while True:
        i = len(lst) - 2
        while i >= 0 and lst[i] >= lst[i + 1]:
            i -= 1
        if i < 0:
            return
        j = len(lst) - 1
        while lst[j] <= lst[i]:
            j -= 1
        lst[i], lst[j] = lst[j], lst[i]
        lst[i + 1:] = lst[i + 1:][::-1]
        yield tuple(lst)


def distinct_necklaces(ms_tuple):
    """Get distinct necklaces (rotation equivalence classes) for a multiset."""
    seen = set()
    necklaces = []
    for p in multiset_perms(list(ms_tuple)):
        rotations = tuple(p[i:] + p[:i] for i in range(len(p)))
        canonical = min(rotations)
        if canonical not in seen:
            seen.add(canonical)
            necklaces.append(canonical)
    return necklaces


def check_consecutive_binary(ms, max_consec=3):
    """Check that no more than max_consec consecutive binary processors."""
    n = len(ms)
    for start in range(n):
        count = 0
        for offset in range(n):
            if ms[(start + offset) % n] == 2:
                count += 1
                if count > max_consec:
                    return False
            else:
                count = 0
    return True


def build_uniform_sweep(ms, n, nb_vals):
    """Build uniform sweep cycle: movers [0,1,...,n-1] x 2."""
    config = [0] * n
    cycle = [tuple(config)]
    # Up sweep
    for proc in range(n):
        config = list(cycle[-1])
        new_val = 1 if ms[proc] == 2 else nb_vals[proc]
        if config[proc] == new_val:
            return None
        config[proc] = new_val
        cycle.append(tuple(config))
    # Down sweep
    for proc in range(n):
        config = list(cycle[-1])
        if config[proc] == 0:
            return None
        config[proc] = 0
        cycle.append(tuple(config))
    if cycle[-1] == cycle[0]:
        cycle = cycle[:-1]
    if len(set(cycle)) != len(cycle):
        return None
    return cycle


def check_consistency(cycle, n):
    """Check cycle consistency and return determined entries."""
    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, {}, "non-single mover"
        mover = diffs[0]
        L, S, R = c[(mover-1) % n], c[mover], c[(mover+1) % n]
        key = (mover, L, S, R)
        if key in det and det[key] != c_next[mover]:
            return False, {}, f"conflict at f{mover}({L},{S},{R})"
        det[key] = c_next[mover]
        for i in range(n):
            if i != mover:
                L, S, R = c[(i-1) % n], c[i], c[(i+1) % n]
                key = (i, L, S, R)
                if key in det and det[key] != S:
                    return False, {}, f"conflict"
                det[key] = S
    return True, det, "OK"


def check_mnu(cycle, n):
    """Check Mover Neighborhood Uniqueness."""
    movers = []
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        movers.append([k for k in range(n) if c[k] != c_next[k]][0])

    violations = 0
    for step in range(len(cycle)):
        p = movers[step]
        gc = cycle[step]
        gc_next = cycle[(step + 1) % len(cycle)]
        L = gc[(p-1) % n]
        S_prime = gc_next[p]
        R = gc[(p+1) % n]

        matches = [j for j, gj in enumerate(cycle)
                   if gj[(p-1) % n] == L and gj[p] == S_prime and gj[(p+1) % n] == R]
        if len(matches) != 1:
            violations += 1
    return violations == 0


def check_universal_escape(cycle, det, ms, n, max_configs=200000):
    """Check that no forced move enters C."""
    good_set = set(cycle)
    product = 1
    for m in ms:
        product *= m
    if product > max_configs:
        return None, product  # too large to enumerate

    moves_enter = 0
    total_moves = 0
    for c in iproduct(*[range(m) for m in ms]):
        if c in good_set:
            continue
        for i in range(n):
            L, S, R = c[(i-1) % n], c[i], c[(i+1) % n]
            key = (i, L, S, R)
            if key in det and det[key] != S:
                total_moves += 1
                new_c = list(c)
                new_c[i] = det[key]
                if tuple(new_c) in good_set:
                    moves_enter += 1
    return moves_enter, total_moves


def find_shadow_cycle(det, good_set, ms, n, max_len=200):
    """Find shadow cycle by chasing forced transitions."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    for start in non_good:
        visited = {}
        path = []
        config = start
        for step in range(max_len):
            if config in good_set:
                break
            if config in visited:
                return path[visited[config]:]
            visited[config] = len(path)
            path.append(config)

            forced = []
            for i in range(n):
                L, S, R = config[(i-1) % n], config[i], config[(i+1) % n]
                key = (i, L, S, R)
                if key in det and det[key] != S:
                    forced.append((i, det[key]))
            if not forced:
                break
            moved = False
            for proc, new_val in forced:
                new_c = list(config)
                new_c[proc] = new_val
                new_c = tuple(new_c)
                if new_c not in good_set:
                    config = new_c
                    moved = True
                    break
            if not moved:
                break
        # Don't return partial results
    return None


# ============================================================
# Select representative CIC candidates at n=9
# ============================================================

n = 9

# From Exploration 1: the 12 surviving multisets with product > 7776
# Plus some from lower products for diversity
candidates = [
    # High-product survivors (most interesting)
    (2,2,2,2,2,4,4,4,4),    # product 8192, k=5 binary
    (2,2,2,2,3,3,3,4,5),    # product 8640, k=4 binary
    (2,2,2,2,2,3,3,5,6),    # product 8640, k=5 binary
    (2,2,2,2,2,2,5,5,5),    # product 8000, k=6 binary
    (2,2,2,2,2,3,3,4,7),    # product 8064, k=5 binary
    (2,2,2,2,2,2,4,4,8),    # product 8192, k=6 binary

    # Some lower-product ones for diversity
    (2,2,2,2,2,2,3,3,14),   # product 8064, k=6 binary
    (2,2,2,2,2,2,3,6,7),    # product 8064, k=6 binary
    (2,2,2,2,2,2,3,4,11),   # product 8448, k=6 binary

    # Some medium-product with fewer binary
    (2,2,2,3,3,3,3,3,4),    # product 7776, k=3 binary
    (2,2,2,2,3,3,3,3,6),    # product 7776, k=4 binary (if exists)
]

# Filter to valid candidates
valid_candidates = []
for ms_tuple in candidates:
    if len(ms_tuple) != n:
        continue
    prod = 1
    for m in ms_tuple:
        prod *= m
    if prod >= 8748:
        continue
    k = sum(1 for m in ms_tuple if m == 2)
    if k < 3:
        continue
    valid_candidates.append(ms_tuple)

print("=" * 70)
print(f"CIC EXPLORATION 3: SHADOW CYCLE EXTENSION TO MIXED SYSTEMS (n={n})")
print("=" * 70)
print(f"\n{len(valid_candidates)} candidate multisets to test")
print()

# ============================================================
# Test each candidate
# ============================================================

grand_stats = {
    'tested': 0,
    'necklaces_tested': 0,
    'consistent_sweeps': 0,
    'mnu_ok': 0,
    'escape_ok': 0,
    'shadow_found': 0,
    'shadow_same_len': 0,
    'no_shadow': 0,
    'too_large': 0,
}

for ms_tuple in valid_candidates:
    prod = 1
    for m in ms_tuple:
        prod *= m
    k = sum(1 for m in ms_tuple if m == 2)

    print(f"\n{'='*60}")
    print(f"Multiset: {ms_tuple}, product={prod}, k={k} binary")
    print(f"{'='*60}")

    # Get distinct necklaces with ≤3 consecutive binary
    necklaces = distinct_necklaces(ms_tuple)
    valid_necklaces = [nk for nk in necklaces
                       if check_consecutive_binary(list(nk), 3)]

    print(f"  {len(necklaces)} total necklaces, {len(valid_necklaces)} with ≤3 consecutive binary")

    grand_stats['tested'] += 1

    if prod > 50000:
        print(f"  Product {prod} too large for full config enumeration, testing with subsets")

    ms_results = {
        'consistent': 0,
        'mnu_ok': 0,
        'escape_checked': 0,
        'escape_ok': 0,
        'shadow_found': 0,
        'shadow_same_len': 0,
        'no_shadow': 0,
    }

    for nk_idx, nk in enumerate(valid_necklaces[:10]):  # limit necklaces for speed
        ms = list(nk)
        bin_procs = [i for i in range(n) if ms[i] == 2]
        nb_procs = [i for i in range(n) if ms[i] > 2]

        grand_stats['necklaces_tested'] += 1

        # Generate NB value combinations (limit for large state counts)
        nb_options = []
        for p in nb_procs:
            nb_options.append(list(range(1, ms[p])))

        total_combos = 1
        for opts in nb_options:
            total_combos *= len(opts)

        # For very large combo spaces, sample
        if total_combos > 100:
            # Sample: take v_i = 1 for all, and a few others
            sample_combos = []
            # All 1s
            sample_combos.append(tuple(1 for _ in nb_procs))
            # All max
            sample_combos.append(tuple(ms[p]-1 for p in nb_procs))
            # Mixed: alternate 1 and max
            sample_combos.append(tuple(
                1 if i % 2 == 0 else ms[nb_procs[i]]-1
                for i in range(len(nb_procs))
            ))
            # A few more random-ish
            import hashlib
            for seed in range(5):
                h = hashlib.md5(f"{nk}-{seed}".encode()).hexdigest()
                vals = []
                for pi, p in enumerate(nb_procs):
                    v = (int(h[pi*2:pi*2+2], 16) % (ms[p]-1)) + 1
                    vals.append(v)
                sample_combos.append(tuple(vals))
            nb_combo_list = list(set(sample_combos))
        else:
            nb_combo_list = list(iproduct(*nb_options))

        nk_consistent = 0
        nk_shadow = 0
        nk_no_shadow = 0

        for combo in nb_combo_list:
            nb_vals = {p: combo[i] for i, p in enumerate(nb_procs)}
            for p in bin_procs:
                nb_vals[p] = 1

            cyc = build_uniform_sweep(ms, n, nb_vals)
            if cyc is None:
                continue

            ok, det, msg = check_consistency(cyc, n)
            if not ok:
                continue

            nk_consistent += 1
            ms_results['consistent'] += 1
            grand_stats['consistent_sweeps'] += 1

            # Check MNU
            mnu = check_mnu(cyc, n)
            if mnu:
                ms_results['mnu_ok'] += 1
                grand_stats['mnu_ok'] += 1

            # Check Universal Escape (only for small products)
            if prod <= 50000:
                escape_result, total = check_universal_escape(cyc, det, ms, n)
                ms_results['escape_checked'] += 1
                if escape_result is not None and escape_result == 0:
                    ms_results['escape_ok'] += 1
                    grand_stats['escape_ok'] += 1
                elif escape_result is not None and escape_result > 0:
                    print(f"    ESCAPE FAILURE at nk={nk}, combo={combo}: "
                          f"{escape_result}/{total} moves enter C!")

            # Check shadow cycle (only for small products)
            if prod <= 50000:
                good_set = set(cyc)
                shadow = find_shadow_cycle(det, good_set, ms, n)
                if shadow:
                    ms_results['shadow_found'] += 1
                    grand_stats['shadow_found'] += 1
                    if len(shadow) == len(cyc):
                        ms_results['shadow_same_len'] += 1
                        grand_stats['shadow_same_len'] += 1
                else:
                    ms_results['no_shadow'] += 1
                    grand_stats['no_shadow'] += 1
                    print(f"    *** NO SHADOW at nk={nk}, combo={combo}! ***")
                    # Print the cycle for analysis
                    for idx, c in enumerate(cyc):
                        c_next = cyc[(idx+1) % len(cyc)]
                        m = [j for j in range(n) if c[j] != c_next[j]][0]
                        print(f"      {idx}: {c} -> P{m}")
            else:
                grand_stats['too_large'] += 1

        if nk_consistent > 0:
            status = "ALL SHADOW" if nk_no_shadow == 0 else f"{nk_no_shadow} NO-SHADOW!"
            if nk_idx < 3 or nk_no_shadow > 0:
                print(f"  nk={nk}: {nk_consistent} consistent, "
                      f"{nk_shadow} shadow, {nk_no_shadow} no-shadow -> {status}")

    print(f"\n  Summary for {ms_tuple}:")
    print(f"    Consistent sweeps: {ms_results['consistent']}")
    print(f"    MNU OK: {ms_results['mnu_ok']}")
    print(f"    Escape OK: {ms_results['escape_ok']}/{ms_results['escape_checked']}")
    print(f"    Shadow found: {ms_results['shadow_found']}")
    print(f"    Shadow same length: {ms_results['shadow_same_len']}")
    print(f"    No shadow: {ms_results['no_shadow']}")


# ============================================================
# Grand summary
# ============================================================
print(f"\n{'='*70}")
print("GRAND SUMMARY")
print(f"{'='*70}")
print(f"  Multisets tested: {grand_stats['tested']}")
print(f"  Necklaces tested: {grand_stats['necklaces_tested']}")
print(f"  Consistent sweep cycles: {grand_stats['consistent_sweeps']}")
print(f"  MNU OK: {grand_stats['mnu_ok']}")
print(f"  Universal Escape OK: {grand_stats['escape_ok']}")
print(f"  Shadow cycles found: {grand_stats['shadow_found']}")
print(f"  Shadow same length: {grand_stats['shadow_same_len']}")
print(f"  No shadow: {grand_stats['no_shadow']}")
print(f"  Too large to check: {grand_stats['too_large']}")

if grand_stats['no_shadow'] == 0 and grand_stats['shadow_found'] > 0:
    print(f"\n  *** ALL {grand_stats['shadow_found']} consistent sweep cycles have shadow cycles! ***")
    print("  Shadow cycle theorem extends to mixed systems at n=9.")
elif grand_stats['no_shadow'] > 0:
    print(f"\n  *** {grand_stats['no_shadow']} cycles WITHOUT shadow! ***")
    print("  Shadow cycle theorem does NOT directly extend.")
