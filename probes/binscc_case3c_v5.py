#!/usr/bin/env python3
"""binscc_case3c_v5.py — Case 3c: fast shadow check via entry conflict analysis.

Key insight: instead of searching all non-good configs for shadows,
check if the determined entries from the sweep cycle create CONFLICTS
with any possible completion. A conflict = the sweep forces some
non-good config to stay non-good (shadow), proving invalidity.

Optimization: instead of checking all product configs, check only
configs reachable by flipping one component from a good config.
These "boundary" configs are the ones that matter for shadow detection.

Also: for the lower bound proof, we don't need shadow detection.
We just need to show the sweep cycle entries create MOVER/NONMOVER
OVERLAP at some binary processor. This is a LOCAL check.
"""

from itertools import combinations
from collections import Counter
import time
import sys


def generate_non_consec_necklaces(n):
    """Generate non-consecutive-3-binary necklaces for {2^3, 4, 3^(n-4)}."""
    seen = set()
    results = []
    for bin_positions in combinations(range(n), 3):
        bp = sorted(bin_positions)
        has_3_consec = False
        # Check all cyclic triples
        for i in range(3):
            a = bp[i]
            b = bp[(i+1)%3]
            c = bp[(i+2)%3]
            # Are a,b,c three consecutive positions on the ring?
            if (b - a) % n == 1 and (c - b) % n == 1:
                has_3_consec = True
                break
        if has_3_consec:
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
                results.append(canonical)
    return results


def construct_sweep_cycle(ms, n, nb_vals):
    """Uniform sweep: [0,1,...,n-1] up then [0,1,...,n-1] down."""
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


def check_binary_overlap_in_sweep(cycle_configs, ms, n):
    """Check if the sweep cycle creates mover/nonmover overlap at a binary proc.

    This is a DIRECT overlap check — doesn't need shadow detection.
    """
    L = len(cycle_configs)
    movers = []
    for idx in range(L):
        c = cycle_configs[idx]
        c_next = cycle_configs[(idx + 1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, None
        movers.append(diffs[0])

    for p in range(n):
        if ms[p] != 2:
            continue
        mover_ctx = set()
        nonmover_ctx = set()
        for idx in range(L):
            c = cycle_configs[idx]
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            if movers[idx] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        if mover_ctx & nonmover_ctx:
            return True, p
    return False, None


def check_consistency_and_shadow_fast(cycle_configs, ms, n):
    """Check consistency + fast shadow via boundary search.

    Instead of checking ALL configs, just check configs adjacent to good set.
    """
    L = len(cycle_configs)
    good_set = set(cycle_configs)

    # Build determined entries
    required = {}
    for idx in range(L):
        c = cycle_configs[idx]
        c_next = cycle_configs[(idx + 1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, False
        mover = diffs[0]
        Li = c[(mover-1)%n]; Si = c[mover]; Ri = c[(mover+1)%n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return False, False  # inconsistent
        required[key] = S_new
        for i in range(n):
            if i != mover:
                Li2 = c[(i-1)%n]; Si2 = c[i]; Ri2 = c[(i+1)%n]
                key2 = (i, Li2, Si2, Ri2)
                if key2 in required and required[key2] != Si2:
                    return False, False
                required[key2] = Si2

    # Fast shadow: check boundary configs (1-flip from good)
    for gc in cycle_configs:
        for i in range(n):
            for v in range(ms[i]):
                if v == gc[i]:
                    continue
                bc = list(gc)
                bc[i] = v
                bc = tuple(bc)
                if bc in good_set:
                    continue
                # Follow chain from bc
                config = bc
                visited = set()
                found_shadow = False
                for step in range(200):
                    if config in good_set:
                        break
                    if config in visited:
                        found_shadow = True
                        break
                    visited.add(config)
                    forced = []
                    for j in range(n):
                        Lj = config[(j-1)%n]; Sj = config[j]; Rj = config[(j+1)%n]
                        key = (j, Lj, Sj, Rj)
                        if key in required and required[key] != Sj:
                            forced.append((j, required[key]))
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
                if found_shadow:
                    return True, True  # consistent + shadow found

    return True, False  # consistent but no shadow


def main():
    print("=" * 70)
    print("CASE 3c: Non-Consecutive {2^3, 4, 3^(n-4)} — Fast Analysis")
    print("=" * 70)
    sys.stdout.flush()

    all_results = {}

    for n in range(5, 19):
        t0 = time.time()
        non_consec = generate_non_consec_necklaces(n)

        if not non_consec:
            print(f"  n={n:2d}: 0 non-consec → vacuous")
            sys.stdout.flush()
            continue

        # Limit sample for large n
        if n > 12:
            sample = non_consec[:min(10, len(non_consec))]
        else:
            sample = non_consec

        total_consistent = 0
        total_overlap = 0
        total_shadow = 0
        total_clean = 0

        for ms_tuple in sample:
            ms = list(ms_tuple)
            nb_procs = [i for i in range(n) if ms[i] > 2]

            # For n ≤ 10: test all NB combos
            # For n > 10: test representative NB values
            if n <= 10:
                nb_combos = [[]]
                for p in nb_procs:
                    new_combos = []
                    for combo in nb_combos:
                        for v in range(1, ms[p]):
                            new_combos.append(combo + [(p, v)])
                    nb_combos = new_combos
                nv_list = [{p: v for p, v in combo} for combo in nb_combos]
            else:
                nv_list = []
                # NB=1 for all
                nv_list.append({p: 1 for p in nb_procs})
                # NB=2 for quaternary
                q_procs = [p for p in range(n) if ms[p] == 4]
                if q_procs:
                    nv2 = {p: 1 for p in nb_procs}
                    nv2[q_procs[0]] = 2
                    nv_list.append(nv2)
                    nv3 = {p: 1 for p in nb_procs}
                    nv3[q_procs[0]] = 3
                    nv_list.append(nv3)
                # NB=2 for all ternary
                nv_list.append({p: 2 for p in nb_procs})

            for nv in nv_list:
                cyc = construct_sweep_cycle(ms, n, nv)
                if not cyc:
                    continue

                # Direct overlap check (fast)
                has_ovlp, proc = check_binary_overlap_in_sweep(cyc, ms, n)
                if has_ovlp:
                    total_consistent += 1
                    total_overlap += 1
                    continue

                # No direct overlap → check consistency + shadow
                consistent, has_shadow = check_consistency_and_shadow_fast(cyc, ms, n)
                if not consistent:
                    continue
                total_consistent += 1
                if has_shadow:
                    total_shadow += 1
                else:
                    total_clean += 1
                    print(f"    CLEAN: n={n} ms={ms_tuple} nv={nv}")
                    sys.stdout.flush()

        elapsed = time.time() - t0
        all_results[n] = (len(non_consec), len(sample), total_consistent,
                          total_overlap, total_shadow, total_clean)

        sampled = f" (sampled {len(sample)}/{len(non_consec)})" if len(sample) < len(non_consec) else ""

        if total_clean == 0 and total_consistent > 0:
            status = f"★ ALL BLOCKED ({total_overlap} overlap + {total_shadow} shadow)"
        elif total_consistent == 0:
            status = "no consistent sweeps"
        else:
            status = f"{total_clean} CLEAN"

        print(f"  n={n:2d}: {len(non_consec):5d} necklaces, "
              f"{total_consistent:5d} consistent → {status}{sampled} "
              f"({elapsed:.1f}s)")
        sys.stdout.flush()

    # ================================================================
    # Summary table
    # ================================================================
    print(f"\n{'='*70}")
    print("SUMMARY TABLE")
    print("="*70)
    print(f"{'n':>3s} {'necklaces':>10s} {'tested':>8s} {'consistent':>11s} "
          f"{'overlap':>8s} {'shadow':>8s} {'clean':>6s} {'status':>12s}")
    print("-" * 70)

    for n in sorted(all_results.keys()):
        nk, samp, cons, ovlp, shad, clean = all_results[n]
        status = "BLOCKED" if clean == 0 and cons > 0 else ("CLEAN" if clean > 0 else "N/A")
        print(f"{n:3d} {nk:10d} {samp:8d} {cons:11d} "
              f"{ovlp:8d} {shad:8d} {clean:6d} {status:>12s}")


if __name__ == "__main__":
    main()
