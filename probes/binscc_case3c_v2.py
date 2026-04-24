#!/usr/bin/env python3
"""binscc_case3c_v2.py — Close Case 3c via shadow cycle + consistency analysis.

For {2^3, 4, 3^(n-4)} with NON-CONSECUTIVE binary placements:
1. Construct sweep cycles (uniform mover order, various NB values)
2. Check consistency (no entry conflicts)
3. Look for shadow cycles (non-good cycles forced by determined entries)
4. If every consistent sweep has a shadow → multiset is blocked

This adapts the shadow_4binary.py approach to 3 binary + 1 quaternary.
"""

from itertools import product as iproduct, permutations
from collections import Counter


def generate_necklaces(ms_list, n):
    """Generate topologically distinct ring orientations of a multiset."""
    ms_tuple = tuple(sorted(ms_list))
    seen = set()
    results = []
    for perm in set(permutations(ms_tuple)):
        rotations = [perm[i:] + perm[:i] for i in range(n)]
        reflected = perm[::-1]
        ref_rotations = [reflected[i:] + reflected[:i] for i in range(n)]
        canonical = min(rotations + ref_rotations)
        if canonical not in seen:
            seen.add(canonical)
            results.append(perm)
    return results


def has_3_consecutive_binary(ms):
    n = len(ms)
    for i in range(n):
        if ms[i] == 2 and ms[(i+1)%n] == 2 and ms[(i+2)%n] == 2:
            return True
    return False


def check_cycle_consistency(cycle_configs, n, ms):
    """Check if a cycle creates no entry conflicts.
    Returns (ok, determined_entries, message)."""
    L = len(cycle_configs)
    required = {}
    for idx in range(L):
        c = cycle_configs[idx]
        c_next = cycle_configs[(idx + 1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, {}, f"non-single mover at step {idx}"
        mover = diffs[0]
        Li = c[(mover - 1) % n]
        Si = c[mover]
        Ri = c[(mover + 1) % n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return False, {}, f"conflict at f{mover}({Li},{Si},{Ri})"
        required[key] = S_new
        # Nonmover entries
        for i in range(n):
            if i != mover:
                Li2 = c[(i - 1) % n]
                Si2 = c[i]
                Ri2 = c[(i + 1) % n]
                key2 = (i, Li2, Si2, Ri2)
                if key2 in required and required[key2] != Si2:
                    return False, {}, f"conflict at f{i}({Li2},{Si2},{Ri2})"
                required[key2] = Si2
    return True, required, "OK"


def find_shadow_cycle(determined, good_set, ms, n, max_len=100):
    """Look for a non-good cycle forced by determined entries."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    for start in non_good:
        visited = set()
        path = []
        config = start
        for step in range(max_len + 1):
            if config in good_set:
                break
            if config in visited:
                cycle_start = path.index(config)
                return path[cycle_start:]
            visited.add(config)
            path.append(config)
            forced = []
            for i in range(n):
                L = config[(i - 1) % n]
                S = config[i]
                R = config[(i + 1) % n]
                key = (i, L, S, R)
                if key in determined and determined[key] != S:
                    forced.append((i, determined[key]))
            if not forced:
                break
            # Fire the first forced processor that stays non-good
            moved = False
            for proc, new_val in forced:
                new_config = list(config)
                new_config[proc] = new_val
                new_config = tuple(new_config)
                if new_config not in good_set:
                    config = new_config
                    moved = True
                    break
            if not moved:
                # All forced moves lead to good → convergence (no shadow here)
                break
    return None


def construct_sweep_cycle(ms, n, nb_vals):
    """Uniform sweep: movers [0,1,...,n-1] × 2.
    First pass: each proc goes 0 → nb_vals[proc].
    Second pass: each proc goes back → 0.
    """
    cycle = []
    config = [0] * n
    cycle.append(tuple(config))

    for proc in range(n):
        config = list(cycle[-1])
        new_val = 1 if ms[proc] == 2 else nb_vals.get(proc, 1)
        if config[proc] == new_val:
            return None  # no change → invalid
        config[proc] = new_val
        cycle.append(tuple(config))

    for proc in range(n):
        config = list(cycle[-1])
        if config[proc] == 0:
            return None  # already at 0 → invalid
        config[proc] = 0
        cycle.append(tuple(config))

    if cycle[-1] == cycle[0]:
        cycle = cycle[:-1]
    if len(set(cycle)) != len(cycle):
        return None  # non-distinct configs
    return cycle


def check_binary_overlap(cycle_configs, ms, n):
    """Check if any binary processor has mover/nonmover overlap."""
    L = len(cycle_configs)
    for p in range(n):
        if ms[p] != 2:
            continue
        mover_ctx = set()
        nonmover_ctx = set()
        for idx in range(L):
            c = cycle_configs[idx]
            c_next = cycle_configs[(idx + 1) % L]
            diffs = [j for j in range(n) if c[j] != c_next[j]]
            mover = diffs[0]
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            if mover == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        if mover_ctx & nonmover_ctx:
            return True, p
    return False, None


def main():
    print("=" * 70)
    print("CASE 3c: Non-Consecutive {2^3, 4, 3^(n-4)} — Shadow Analysis")
    print("=" * 70)

    for n in range(5, 10):
        ms_base = [2, 2, 2, 4] + [3] * (n - 4)
        necklaces = generate_necklaces(ms_base, n)
        non_consec = [ms for ms in necklaces if not has_3_consecutive_binary(ms)]
        consec = [ms for ms in necklaces if has_3_consecutive_binary(ms)]

        product = 1
        for m in ms_base:
            product *= m

        print(f"\nn={n}: product={product}, {len(necklaces)} orientations, "
              f"{len(consec)} consecutive, {len(non_consec)} non-consecutive")

        if not non_consec:
            print("  No non-consecutive orientations → Case 3c vacuous")
            continue

        # For each non-consecutive orientation:
        total_consistent = 0
        total_shadow = 0
        total_overlap = 0
        total_clean = 0
        orientations_fully_blocked = 0

        for ms_tuple in non_consec:
            ms = list(ms_tuple)
            nb_procs = [i for i in range(n) if ms[i] > 2]

            # Generate all NB value combinations
            nb_combos = [[]]
            for p in nb_procs:
                new_combos = []
                for combo in nb_combos:
                    for v in range(1, ms[p]):
                        new_combos.append(combo + [(p, v)])
                nb_combos = new_combos

            ms_consistent = 0
            ms_shadow = 0
            ms_overlap = 0

            for combo in nb_combos:
                nv = {p: v for p, v in combo}
                cyc = construct_sweep_cycle(ms, n, nv)
                if not cyc:
                    continue

                ok, det, msg = check_cycle_consistency(cyc, n, ms)
                if not ok:
                    continue

                ms_consistent += 1

                # Check binary overlap on the sweep cycle itself
                has_ovlp, proc = check_binary_overlap(cyc, ms, n)
                if has_ovlp:
                    ms_overlap += 1
                    continue

                # No direct overlap → check for shadow cycle
                good_set = set(map(tuple, cyc))
                shadow = find_shadow_cycle(det, good_set, ms, n)
                if shadow:
                    ms_shadow += 1

            blocked = ms_consistent > 0 and (ms_overlap + ms_shadow == ms_consistent)
            if blocked:
                orientations_fully_blocked += 1

            total_consistent += ms_consistent
            total_shadow += ms_shadow
            total_overlap += ms_overlap
            total_clean += max(0, ms_consistent - ms_overlap - ms_shadow)

            if ms_consistent > 0:
                clean = ms_consistent - ms_overlap - ms_shadow
                status = "BLOCKED" if clean == 0 else f"{clean} CLEAN"
                if clean > 0:
                    print(f"  ms={ms_tuple}: {ms_consistent} consistent, "
                          f"{ms_overlap} overlap, {ms_shadow} shadow, "
                          f"{clean} clean → {status}")

        if total_clean == 0 and total_consistent > 0:
            print(f"  ★ ALL {len(non_consec)} non-consec orientations BLOCKED "
                  f"({total_consistent} consistent: {total_overlap} overlap, "
                  f"{total_shadow} shadow)")
        elif total_consistent == 0:
            print(f"  No consistent sweep cycles found")
        else:
            print(f"  PARTIAL: {orientations_fully_blocked}/{len(non_consec)} blocked, "
                  f"{total_clean} clean cycles remain")

    # ================================================================
    # Additional analysis: try non-uniform NB values and reverse sweeps
    # ================================================================
    print(f"\n{'='*70}")
    print("ADDITIONAL: Reverse sweep + extended patterns")
    print("="*70)

    for n in [5, 6, 7, 8, 9]:
        ms_base = [2, 2, 2, 4] + [3] * (n - 4)
        necklaces = generate_necklaces(ms_base, n)
        non_consec = [ms for ms in necklaces if not has_3_consecutive_binary(ms)]

        if not non_consec:
            continue

        any_clean = False

        for ms_tuple in non_consec:
            ms = list(ms_tuple)
            nb_procs = [i for i in range(n) if ms[i] > 2]

            # Try REVERSE sweep: movers [n-1, n-2, ..., 0] × 2
            nb_combos = [[]]
            for p in nb_procs:
                new_combos = []
                for combo in nb_combos:
                    for v in range(1, ms[p]):
                        new_combos.append(combo + [(p, v)])
                nb_combos = new_combos

            for combo in nb_combos:
                nv = {p: v for p, v in combo}

                # Reverse sweep
                cycle = []
                config = [0] * n
                cycle.append(tuple(config))
                valid = True
                for proc in range(n-1, -1, -1):
                    config = list(cycle[-1])
                    new_val = 1 if ms[proc] == 2 else nv.get(proc, 1)
                    if config[proc] == new_val:
                        valid = False
                        break
                    config[proc] = new_val
                    cycle.append(tuple(config))
                if not valid:
                    continue
                for proc in range(n-1, -1, -1):
                    config = list(cycle[-1])
                    if config[proc] == 0:
                        valid = False
                        break
                    config[proc] = 0
                    cycle.append(tuple(config))
                if not valid:
                    continue
                if cycle[-1] == cycle[0]:
                    cycle = cycle[:-1]
                if len(set(cycle)) != len(cycle):
                    continue

                ok, det, msg = check_cycle_consistency(cycle, n, ms)
                if not ok:
                    continue

                has_ovlp, proc = check_binary_overlap(cycle, ms, n)
                if has_ovlp:
                    continue

                good_set = set(map(tuple, cycle))
                shadow = find_shadow_cycle(det, good_set, ms, n)
                if not shadow:
                    any_clean = True
                    print(f"  n={n} ms={ms_tuple} rev-sweep nv={nv}: CLEAN (no shadow)")

        if not any_clean:
            print(f"  n={n}: ALL reverse sweeps also blocked")


if __name__ == "__main__":
    main()
