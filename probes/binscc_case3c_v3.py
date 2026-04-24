#!/usr/bin/env python3
"""binscc_case3c_v3.py — Extend Case 3c to larger n, test robustness.

1. Shadow analysis for n=5..14 (all non-consecutive orientations)
2. Non-uniform sweep patterns (different NB orders)
3. Structural analysis: why do shadows always exist?
"""

from itertools import product as iproduct, permutations
from collections import Counter
import time


def generate_necklaces(ms_list, n):
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
    L = len(cycle_configs)
    required = {}
    for idx in range(L):
        c = cycle_configs[idx]
        c_next = cycle_configs[(idx + 1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, {}, "non-single"
        mover = diffs[0]
        Li = c[(mover - 1) % n]; Si = c[mover]; Ri = c[(mover + 1) % n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return False, {}, "conflict"
        required[key] = S_new
        for i in range(n):
            if i != mover:
                Li2 = c[(i-1)%n]; Si2 = c[i]; Ri2 = c[(i+1)%n]
                key2 = (i, Li2, Si2, Ri2)
                if key2 in required and required[key2] != Si2:
                    return False, {}, "conflict"
                required[key2] = Si2
    return True, required, "OK"


def find_shadow_cycle(determined, good_set, ms, n, max_len=200):
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
                L = config[(i-1)%n]; S = config[i]; R = config[(i+1)%n]
                key = (i, L, S, R)
                if key in determined and determined[key] != S:
                    forced.append((i, determined[key]))
            if not forced:
                break
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
                break
    return None


def construct_sweep_cycle(ms, n, nb_vals):
    cycle = []
    config = [0] * n
    cycle.append(tuple(config))
    for proc in range(n):
        config = list(cycle[-1])
        new_val = 1 if ms[proc] == 2 else nb_vals.get(proc, 1)
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
    if len(set(cycle)) != len(cycle):
        return None
    return cycle


def main():
    print("=" * 70)
    print("CASE 3c EXTENDED: Shadow Analysis for n=5..14")
    print("=" * 70)

    results = {}

    for n in range(5, 15):
        t0 = time.time()
        ms_base = [2, 2, 2, 4] + [3] * (n - 4)
        product = 1
        for m in ms_base:
            product *= m

        # For large n, necklace generation via permutations is expensive
        # Use a smarter method: place 3 binary + 1 quaternary in n positions
        if n <= 10:
            necklaces = generate_necklaces(ms_base, n)
            non_consec = [ms for ms in necklaces if not has_3_consecutive_binary(ms)]
        else:
            # For n > 10, just test a few representative non-consecutive patterns
            non_consec = []
            # Pattern: binary at 0, spread, spread; quaternary at specific positions
            for q_pos in range(1, n):
                # Place quaternary at q_pos
                # Place 3 binary at maximally separated positions
                remaining = [i for i in range(n) if i != q_pos]
                # Try: binary at 0, n//3, 2*n//3 (approx)
                gap = n // 3
                b_positions = [0, gap, 2*gap]
                # Check none overlap with q_pos
                if q_pos in b_positions:
                    continue
                ms = [3] * n
                for bp in b_positions:
                    ms[bp] = 2
                ms[q_pos] = 4
                ms_tuple = tuple(ms)
                if not has_3_consecutive_binary(ms_tuple):
                    # Normalize
                    rotations = [ms_tuple[i:] + ms_tuple[:i] for i in range(n)]
                    reflected = ms_tuple[::-1]
                    ref_rotations = [reflected[i:] + reflected[:i] for i in range(n)]
                    canonical = min(rotations + ref_rotations)
                    if canonical not in [tuple(x) for x in non_consec]:
                        non_consec.append(canonical)

            # Also try: binary at 0, 2, n-1 (2 consecutive + 1 separated)
            for q_pos in range(3, n-1):
                ms = [3] * n
                ms[0] = 2; ms[2] = 2; ms[n-1] = 2
                ms[q_pos] = 4
                ms_tuple = tuple(ms)
                if not has_3_consecutive_binary(ms_tuple):
                    rotations = [ms_tuple[i:] + ms_tuple[:i] for i in range(n)]
                    reflected = ms_tuple[::-1]
                    ref_rotations = [reflected[i:] + reflected[:i] for i in range(n)]
                    canonical = min(rotations + ref_rotations)
                    if canonical not in [tuple(x) for x in non_consec]:
                        non_consec.append(canonical)

        total_consistent = 0
        total_shadow = 0
        total_clean = 0

        for ms_tuple in non_consec:
            ms = list(ms_tuple)
            nb_procs = [i for i in range(n) if ms[i] > 2]

            # Generate NB value combinations
            nb_combos = [[]]
            for p in nb_procs:
                new_combos = []
                for combo in nb_combos:
                    for v in range(1, ms[p]):
                        new_combos.append(combo + [(p, v)])
                nb_combos = new_combos

            ms_consistent = 0
            ms_shadow = 0

            for combo in nb_combos:
                nv = {p: v for p, v in combo}
                cyc = construct_sweep_cycle(ms, n, nv)
                if not cyc:
                    continue

                ok, det, msg = check_cycle_consistency(cyc, n, ms)
                if not ok:
                    continue

                ms_consistent += 1
                good_set = set(map(tuple, cyc))
                shadow = find_shadow_cycle(det, good_set, ms, n)
                if shadow:
                    ms_shadow += 1

            total_consistent += ms_consistent
            total_shadow += ms_shadow
            total_clean += max(0, ms_consistent - ms_shadow)

        elapsed = time.time() - t0
        results[n] = (len(non_consec), total_consistent, total_shadow, total_clean)

        if total_clean == 0 and total_consistent > 0:
            print(f"  n={n:2d}: {len(non_consec):3d} non-consec, "
                  f"{total_consistent:5d} consistent, "
                  f"{total_shadow:5d} shadow → ★ ALL BLOCKED "
                  f"({elapsed:.1f}s)")
        elif total_consistent == 0:
            print(f"  n={n:2d}: {len(non_consec):3d} non-consec, "
                  f"no consistent sweeps ({elapsed:.1f}s)")
        else:
            print(f"  n={n:2d}: {len(non_consec):3d} non-consec, "
                  f"{total_consistent:5d} consistent, "
                  f"{total_shadow:5d} shadow, "
                  f"{total_clean:3d} CLEAN ({elapsed:.1f}s)")

    # ================================================================
    # Structural analysis: shadow length and structure
    # ================================================================
    print(f"\n{'='*70}")
    print("STRUCTURAL ANALYSIS: Shadow properties at n=5..9")
    print("="*70)

    for n in range(5, 10):
        ms_base = [2, 2, 2, 4] + [3] * (n - 4)
        necklaces = generate_necklaces(ms_base, n)
        non_consec = [ms for ms in necklaces if not has_3_consecutive_binary(ms)]

        shadow_lengths = Counter()
        shadow_movers = Counter()

        for ms_tuple in non_consec[:5]:  # sample
            ms = list(ms_tuple)
            nb_procs = [i for i in range(n) if ms[i] > 2]

            # Just test NB=1 for all
            nv = {p: 1 for p in nb_procs}
            cyc = construct_sweep_cycle(ms, n, nv)
            if not cyc:
                continue

            ok, det, msg = check_cycle_consistency(cyc, n, ms)
            if not ok:
                continue

            good_set = set(map(tuple, cyc))
            shadow = find_shadow_cycle(det, good_set, ms, n)
            if shadow:
                shadow_lengths[len(shadow)] += 1

                # Analyze shadow movers
                shadow_movers_list = []
                for idx in range(len(shadow)):
                    c = shadow[idx]
                    c_next = shadow[(idx + 1) % len(shadow)]
                    diffs = [j for j in range(n) if c[j] != c_next[j]]
                    if len(diffs) == 1:
                        shadow_movers_list.append(diffs[0])
                    else:
                        shadow_movers_list.append(-1)

                # Check which processors fire in shadow
                fire_counts = Counter(shadow_movers_list)
                bin_fires = sum(fire_counts.get(i, 0) for i in range(n) if ms[i] == 2)
                nb_fires = sum(fire_counts.get(i, 0) for i in range(n) if ms[i] > 2)

                if n <= 7:
                    print(f"  n={n} ms={ms_tuple}: shadow len={len(shadow)}, "
                          f"bin_fires={bin_fires}, nb_fires={nb_fires}, "
                          f"movers={shadow_movers_list[:20]}")

        if shadow_lengths:
            print(f"  n={n}: shadow lengths: {dict(shadow_lengths)}")

    # ================================================================
    # Key test: non-uniform sweeps (random mover orders)
    # ================================================================
    print(f"\n{'='*70}")
    print("NON-UNIFORM SWEEPS: random mover orderings")
    print("="*70)

    import random
    random.seed(42)

    for n in [5, 6, 7, 8, 9]:
        ms_base = [2, 2, 2, 4] + [3] * (n - 4)
        necklaces = generate_necklaces(ms_base, n)
        non_consec = [ms for ms in necklaces if not has_3_consecutive_binary(ms)]

        total_tested = 0
        total_clean = 0

        for ms_tuple in non_consec[:10]:
            ms = list(ms_tuple)
            nb_procs = [i for i in range(n) if ms[i] > 2]

            # Try 20 random non-uniform sweep orderings
            for trial in range(20):
                # Random mover order for first half
                order1 = list(range(n))
                random.shuffle(order1)
                # Second half reverses to return to 0
                order2 = list(range(n))
                random.shuffle(order2)

                nv = {p: 1 for p in nb_procs}

                cycle = []
                config = [0] * n
                cycle.append(tuple(config))
                valid = True

                # First half
                for proc in order1:
                    config = list(cycle[-1])
                    new_val = 1 if ms[proc] == 2 else nv.get(proc, 1)
                    if config[proc] == new_val:
                        valid = False
                        break
                    config[proc] = new_val
                    cycle.append(tuple(config))
                if not valid:
                    continue

                # Second half
                for proc in order2:
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

                # Check ring adjacency of movers
                movers = []
                for idx in range(len(cycle)):
                    c = cycle[idx]
                    c_next = cycle[(idx + 1) % len(cycle)]
                    diffs = [j for j in range(n) if c[j] != c_next[j]]
                    if len(diffs) != 1:
                        valid = False
                        break
                    movers.append(diffs[0])
                if not valid:
                    continue

                # Note: non-uniform sweeps may not be ring-adjacent.
                # That's OK — we just need consistency.

                ok, det, msg = check_cycle_consistency(cycle, n, ms)
                if not ok:
                    continue

                total_tested += 1
                good_set = set(map(tuple, cycle))
                shadow = find_shadow_cycle(det, good_set, ms, n)
                if not shadow:
                    total_clean += 1
                    print(f"  n={n} ms={ms_tuple} trial={trial}: CLEAN!")

        if total_clean == 0 and total_tested > 0:
            print(f"  n={n}: {total_tested} non-uniform sweeps tested → ALL BLOCKED")
        elif total_tested == 0:
            print(f"  n={n}: no valid non-uniform sweeps found")


if __name__ == "__main__":
    main()
