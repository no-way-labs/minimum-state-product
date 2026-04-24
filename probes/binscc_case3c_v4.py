#!/usr/bin/env python3
"""binscc_case3c_v4.py — Case 3c: non-consecutive {2^3, 4, 3^(n-4)}.

Fast necklace generation + shadow analysis for n=5..18.
"""

from itertools import product as iproduct, combinations
from collections import Counter
import time


def generate_non_consec_necklaces(n):
    """Generate non-consecutive-3-binary necklaces for {2^3, 4, 3^(n-4)}.

    Place 3 binary processors and 1 quaternary processor on a ring of n,
    rest ternary. Filter out arrangements with 3 consecutive binary.
    Normalize by rotation + reflection.
    """
    seen = set()
    results = []

    # Choose 3 positions for binary out of n
    for bin_positions in combinations(range(n), 3):
        # Check 3-consecutive binary
        bp = sorted(bin_positions)
        has_3_consec = False
        for i in range(3):
            a, b, c = bp[i], bp[(i+1)%3], bp[(i+2)%3]
            # Check if a, b, c are 3 consecutive on the ring
            if (b - a) % n == 1 and (c - b) % n == 1:
                has_3_consec = True
                break
        if has_3_consec:
            continue

        # Choose position for quaternary from remaining
        remaining = [i for i in range(n) if i not in bin_positions]
        for q_pos in remaining:
            ms = [3] * n
            for bp_i in bin_positions:
                ms[bp_i] = 2
            ms[q_pos] = 4
            ms_tuple = tuple(ms)

            # Normalize by rotation + reflection
            rotations = [ms_tuple[i:] + ms_tuple[:i] for i in range(n)]
            reflected = ms_tuple[::-1]
            ref_rotations = [reflected[i:] + reflected[:i] for i in range(n)]
            canonical = min(rotations + ref_rotations)

            if canonical not in seen:
                seen.add(canonical)
                results.append(canonical)

    return results


def check_cycle_consistency(cycle_configs, n, ms):
    L = len(cycle_configs)
    required = {}
    for idx in range(L):
        c = cycle_configs[idx]
        c_next = cycle_configs[(idx + 1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, {}
        mover = diffs[0]
        Li = c[(mover-1)%n]; Si = c[mover]; Ri = c[(mover+1)%n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return False, {}
        required[key] = S_new
        for i in range(n):
            if i != mover:
                Li2 = c[(i-1)%n]; Si2 = c[i]; Ri2 = c[(i+1)%n]
                key2 = (i, Li2, Si2, Ri2)
                if key2 in required and required[key2] != Si2:
                    return False, {}
                required[key2] = Si2
    return True, required


def find_shadow_cycle(determined, good_set, ms, n, max_len=200):
    """Look for non-good cycle forced by determined entries.

    Optimization: instead of iterating all configs, try configs near good set.
    """
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
                return True  # Found a shadow cycle
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
    return False


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
    print("CASE 3c: Shadow Analysis — Fast Necklaces, n=5..18")
    print("=" * 70)

    for n in range(5, 19):
        t0 = time.time()

        non_consec = generate_non_consec_necklaces(n)
        product = (2**3) * 4 * (3**(n-4))

        if not non_consec:
            print(f"  n={n:2d}: 0 non-consec orientations → vacuous")
            continue

        # For n > 12, product is huge — shadow search over all configs is too slow
        # Limit to sampling representative orientations
        if n > 12:
            sample = non_consec[:min(5, len(non_consec))]
        else:
            sample = non_consec

        total_consistent = 0
        total_shadow = 0
        total_clean = 0

        for ms_tuple in sample:
            ms = list(ms_tuple)
            nb_procs = [i for i in range(n) if ms[i] > 2]

            # For large n, limit NB combos
            if n > 10:
                # Just test NB=1 for all non-binary procs
                nb_combos_list = [{p: 1 for p in nb_procs}]
                # Also test NB=2 for quaternary
                q_procs = [p for p in range(n) if ms[p] == 4]
                if q_procs:
                    nv2 = {p: 1 for p in nb_procs}
                    nv2[q_procs[0]] = 2
                    nb_combos_list.append(nv2)
                    nv3 = {p: 1 for p in nb_procs}
                    nv3[q_procs[0]] = 3
                    nb_combos_list.append(nv3)
            else:
                nb_combos = [[]]
                for p in nb_procs:
                    new_combos = []
                    for combo in nb_combos:
                        for v in range(1, ms[p]):
                            new_combos.append(combo + [(p, v)])
                    nb_combos = new_combos
                nb_combos_list = [{p: v for p, v in combo} for combo in nb_combos]

            for nv in nb_combos_list:
                cyc = construct_sweep_cycle(ms, n, nv)
                if not cyc:
                    continue

                ok, det = check_cycle_consistency(cyc, n, ms)
                if not ok:
                    continue

                total_consistent += 1
                good_set = set(map(tuple, cyc))
                has_shadow = find_shadow_cycle(det, good_set, ms, n)
                if has_shadow:
                    total_shadow += 1
                else:
                    total_clean += 1
                    print(f"    CLEAN: n={n} ms={ms_tuple} nv={nv}")

        elapsed = time.time() - t0

        tested_note = f" (sampled {len(sample)}/{len(non_consec)})" if len(sample) < len(non_consec) else ""

        if total_clean == 0 and total_consistent > 0:
            print(f"  n={n:2d}: {len(non_consec):4d} non-consec, "
                  f"{total_consistent:5d} consistent, "
                  f"ALL BLOCKED ★{tested_note} ({elapsed:.1f}s)")
        elif total_consistent == 0:
            print(f"  n={n:2d}: {len(non_consec):4d} non-consec, "
                  f"no consistent sweeps{tested_note} ({elapsed:.1f}s)")
        else:
            print(f"  n={n:2d}: {len(non_consec):4d} non-consec, "
                  f"{total_consistent:5d} consistent, "
                  f"{total_clean:3d} CLEAN{tested_note} ({elapsed:.1f}s)")

    # ================================================================
    # Verify 3-consecutive check is correct
    # ================================================================
    print(f"\n{'='*70}")
    print("SANITY CHECK: Total orientations (consec + non-consec)")
    print("="*70)

    for n in range(5, 11):
        non_consec = generate_non_consec_necklaces(n)

        # Count consecutive necklaces separately
        seen = set()
        consec_count = 0
        for bin_positions in combinations(range(n), 3):
            bp = sorted(bin_positions)
            has_3_consec = False
            for i in range(3):
                a, b, c = bp[i], bp[(i+1)%3], bp[(i+2)%3]
                if (b - a) % n == 1 and (c - b) % n == 1:
                    has_3_consec = True
                    break
            if not has_3_consec:
                continue
            remaining = [i for i in range(n) if i not in bin_positions]
            for q_pos in remaining:
                ms = [3] * n
                for bp_i in bin_positions:
                    ms[bp_i] = 2
                ms[q_pos] = 4
                ms_tuple = tuple(ms)
                rotations = [ms_tuple[i:] + ms_tuple[:i] for i in range(n)]
                reflected = ms_tuple[::-1]
                ref_rotations = [reflected[i:] + reflected[:i] for i in range(n)]
                canonical = min(rotations + ref_rotations)
                if canonical not in seen:
                    seen.add(canonical)
                    consec_count += 1

        print(f"  n={n}: {consec_count} consecutive + {len(non_consec)} non-consecutive "
              f"= {consec_count + len(non_consec)} total")


if __name__ == "__main__":
    main()
