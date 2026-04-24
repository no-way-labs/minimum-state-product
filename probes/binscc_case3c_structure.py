#!/usr/bin/env python3
"""binscc_case3c_structure.py — Structural analysis of WHY shadows exist.

Key questions:
1. What is the shadow cycle structure? (length, movers, pattern)
2. Does the shadow use the same permutation as the pure {2,3} case?
3. What entry conflicts create the shadow?
4. Can we identify a universal pattern that works for all n?
"""

from itertools import product as iproduct, combinations
from collections import Counter
import sys


def generate_non_consec_necklaces(n):
    seen = set()
    results = []
    for bin_positions in combinations(range(n), 3):
        bp = sorted(bin_positions)
        has_3_consec = False
        for i in range(3):
            a, b, c = bp[i], bp[(i+1)%3], bp[(i+2)%3]
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


def find_shadow_with_details(cycle_configs, ms, n):
    """Find shadow cycle and return full details."""
    L = len(cycle_configs)
    good_set = set(cycle_configs)

    # Build determined entries
    required = {}
    for idx in range(L):
        c = cycle_configs[idx]
        c_next = cycle_configs[(idx + 1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return None
        mover = diffs[0]
        Li = c[(mover-1)%n]; Si = c[mover]; Ri = c[(mover+1)%n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return None
        required[key] = S_new
        for i in range(n):
            if i != mover:
                Li2 = c[(i-1)%n]; Si2 = c[i]; Ri2 = c[(i+1)%n]
                key2 = (i, Li2, Si2, Ri2)
                if key2 in required and required[key2] != Si2:
                    return None
                required[key2] = Si2

    # Find shadow from boundary configs
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

                config = bc
                visited = {}
                path = []
                for step in range(200):
                    if config in good_set:
                        break
                    if config in visited:
                        cycle_start = visited[config]
                        shadow = path[cycle_start:]
                        # Get shadow movers
                        shadow_movers = []
                        for sidx in range(len(shadow)):
                            sc = shadow[sidx]
                            sc_next = shadow[(sidx + 1) % len(shadow)]
                            diffs = [j for j in range(n) if sc[j] != sc_next[j]]
                            shadow_movers.append(diffs[0] if len(diffs) == 1 else -1)
                        return {
                            'cycle': shadow,
                            'movers': shadow_movers,
                            'length': len(shadow),
                            'start_config': bc,
                            'source_good': gc,
                            'flip_pos': i,
                        }
                    visited[config] = step
                    path.append(config)
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
    return None


def config_diff(c1, c2):
    """Show which positions differ between two configs."""
    return [(i, c1[i], c2[i]) for i in range(len(c1)) if c1[i] != c2[i]]


def main():
    print("=" * 70)
    print("SHADOW STRUCTURE ANALYSIS: WHY do shadows exist?")
    print("=" * 70)

    for n in range(5, 10):
        ms_base = [2, 2, 2, 4] + [3] * (n - 4)
        non_consec = generate_non_consec_necklaces(n)

        print(f"\n{'='*70}")
        print(f"n={n}")
        print(f"{'='*70}")

        for ms_tuple in non_consec[:3]:  # first 3 orientations
            ms = list(ms_tuple)
            bin_procs = [i for i in range(n) if ms[i] == 2]
            q_procs = [i for i in range(n) if ms[i] == 4]
            ter_procs = [i for i in range(n) if ms[i] == 3]

            nb_procs = [i for i in range(n) if ms[i] > 2]
            nv = {p: 1 for p in nb_procs}
            cyc = construct_sweep_cycle(ms, n, nv)
            if not cyc:
                continue

            print(f"\n  ms={ms_tuple}")
            print(f"  binary at {bin_procs}, quaternary at {q_procs}")

            # Show good cycle
            good_movers = []
            for idx in range(len(cyc)):
                c = cyc[idx]
                c_next = cyc[(idx + 1) % len(cyc)]
                diffs = [j for j in range(n) if c[j] != c_next[j]]
                good_movers.append(diffs[0])

            print(f"  Good cycle (len={len(cyc)}): movers={good_movers}")
            for idx, c in enumerate(cyc[:min(12, len(cyc))]):
                print(f"    g[{idx:2d}] = {c}  → P{good_movers[idx]}")
            if len(cyc) > 12:
                print(f"    ... ({len(cyc)-12} more)")

            # Find shadow
            result = find_shadow_with_details(cyc, ms, n)
            if result:
                shadow = result['cycle']
                shadow_movers = result['movers']
                print(f"\n  Shadow (len={result['length']}): movers={shadow_movers}")
                print(f"  Entry point: flip position {result['flip_pos']} of good config")

                for sidx, sc in enumerate(shadow[:min(12, len(shadow))]):
                    print(f"    s[{sidx:2d}] = {sc}  → P{shadow_movers[sidx]}")
                if len(shadow) > 12:
                    print(f"    ... ({len(shadow)-12} more)")

                # Analyze: which good config does each shadow config come from?
                good_set = set(cyc)
                print(f"\n  Shadow-Good relationships:")
                for sidx, sc in enumerate(shadow):
                    # Find closest good config (by Hamming distance)
                    min_dist = n + 1
                    closest = None
                    for gidx, gc in enumerate(cyc):
                        dist = sum(1 for i in range(n) if sc[i] != gc[i])
                        if dist < min_dist:
                            min_dist = dist
                            closest = gidx
                    print(f"    s[{sidx}]={sc} closest to g[{closest}] "
                          f"(dist={min_dist}) diffs={config_diff(sc, cyc[closest])}")

                # Shadow cycle fire counts
                fire_counts = Counter(shadow_movers)
                print(f"\n  Shadow fire counts: {dict(fire_counts)}")
                for p in range(n):
                    if p in fire_counts:
                        mod_check = fire_counts[p] % ms[p]
                        print(f"    P{p} (m={ms[p]}): fires {fire_counts[p]}, "
                              f"mod m = {mod_check}")

                # Compare good vs shadow movers
                print(f"\n  Good movers:   {good_movers}")
                print(f"  Shadow movers: {shadow_movers}")

                # Check if shadow is a permutation of good
                if len(shadow) == len(cyc):
                    # Check if shadow movers are a permutation of good movers
                    gm_sorted = sorted(good_movers)
                    sm_sorted = sorted(shadow_movers)
                    print(f"  Same length: {len(shadow) == len(cyc)}")
                    print(f"  Same mover multiset: {gm_sorted == sm_sorted}")

                    # Find permutation σ: shadow_movers[k] = good_movers[σ(k)]?
                    # This would be the shadow permutation
                    for offset in range(len(cyc)):
                        match = True
                        for k in range(len(cyc)):
                            if shadow_movers[k] != good_movers[(k + offset) % len(cyc)]:
                                match = False
                                break
                        if match:
                            print(f"  Shadow = Good shifted by {offset}")
                            break
            else:
                print("  No shadow found (unexpected!)")

    # ================================================================
    # KEY QUESTION: What makes the shadow work with quaternary?
    # ================================================================
    print(f"\n{'='*70}")
    print("KEY QUESTION: What role does the quaternary processor play?")
    print("="*70)

    # Compare: same binary positions, quaternary vs ternary
    for n in [6, 7, 8]:
        ms_base = [2, 2, 2, 4] + [3] * (n - 4)
        non_consec = generate_non_consec_necklaces(n)

        # For each non-consec, compare with the pure {2,3} version
        for ms_tuple in non_consec[:2]:
            ms_q = list(ms_tuple)
            q_pos = [i for i in range(n) if ms_q[i] == 4][0]
            ms_t = list(ms_tuple)
            ms_t[q_pos] = 3  # Replace quaternary with ternary

            print(f"\n  n={n}: quaternary at P{q_pos}")
            print(f"    ms_q={ms_q}")
            print(f"    ms_t={ms_t}")

            nb_q = [i for i in range(n) if ms_q[i] > 2]
            nb_t = [i for i in range(n) if ms_t[i] > 2]
            nv_q = {p: 1 for p in nb_q}
            nv_t = {p: 1 for p in nb_t}

            cyc_q = construct_sweep_cycle(ms_q, n, nv_q)
            cyc_t = construct_sweep_cycle(ms_t, n, nv_t)

            if cyc_q and cyc_t:
                # Both have same structure (just different ms)
                # Check if they produce the same good configs (modulo quaternary value)
                same = all(
                    all(cyc_q[k][i] == cyc_t[k][i] for i in range(n) if i != q_pos)
                    for k in range(min(len(cyc_q), len(cyc_t)))
                )
                print(f"    Same non-q values: {same}")
                print(f"    Cycle lengths: q={len(cyc_q)}, t={len(cyc_t)}")

                shadow_q = find_shadow_with_details(cyc_q, ms_q, n)
                shadow_t = find_shadow_with_details(cyc_t, ms_t, n)

                sq_len = shadow_q['length'] if shadow_q else 0
                st_len = shadow_t['length'] if shadow_t else 0
                print(f"    Shadow lengths: q={sq_len}, t={st_len}")

                if shadow_q and shadow_t:
                    print(f"    Shadow movers (q): {shadow_q['movers']}")
                    print(f"    Shadow movers (t): {shadow_t['movers']}")
                    print(f"    Same shadow movers: {shadow_q['movers'] == shadow_t['movers']}")

    # ================================================================
    # Entry analysis: which entries create the shadow?
    # ================================================================
    print(f"\n{'='*70}")
    print("ENTRY CONFLICT ANALYSIS: What forces the shadow?")
    print("="*70)

    n = 7
    ms_base = [2, 2, 2, 4] + [3] * (n - 4)
    non_consec = generate_non_consec_necklaces(n)

    for ms_tuple in non_consec[:2]:
        ms = list(ms_tuple)
        nb_procs = [i for i in range(n) if ms[i] > 2]
        nv = {p: 1 for p in nb_procs}
        cyc = construct_sweep_cycle(ms, n, nv)
        if not cyc:
            continue

        good_set = set(cyc)

        # Build ALL determined entries
        required = {}
        for idx in range(len(cyc)):
            c = cyc[idx]
            c_next = cyc[(idx + 1) % len(cyc)]
            diffs = [j for j in range(n) if c[j] != c_next[j]]
            mover = diffs[0]

            # Mover entry
            Li = c[(mover-1)%n]; Si = c[mover]; Ri = c[(mover+1)%n]
            S_new = c_next[mover]
            key = (mover, Li, Si, Ri)
            required[key] = S_new

            # Nonmover entries
            for i in range(n):
                if i != mover:
                    Li2 = c[(i-1)%n]; Si2 = c[i]; Ri2 = c[(i+1)%n]
                    key2 = (i, Li2, Si2, Ri2)
                    required[key2] = Si2

        # Count entries by type
        print(f"\n  ms={ms_tuple}")
        mover_entries = {}
        nonmover_entries = {}

        for idx in range(len(cyc)):
            c = cyc[idx]
            c_next = cyc[(idx + 1) % len(cyc)]
            diffs = [j for j in range(n) if c[j] != c_next[j]]
            mover = diffs[0]
            Li = c[(mover-1)%n]; Si = c[mover]; Ri = c[(mover+1)%n]
            S_new = c_next[mover]
            mover_entries[(mover, Li, Si, Ri)] = S_new

        # Identify overlap entries (same context appears as mover AND nonmover)
        # But with different required outputs
        overlap_count = 0
        for key in mover_entries:
            proc, L, S, R = key
            # The mover entry says: when P fires with context (L,S,R), output changes to S'
            # A nonmover entry with SAME (L,S,R) would say: output stays at S
            # If the mover changes S, then S' != S, creating an entry conflict
            # when the context (L,S,R) appears as both mover and nonmover
            if mover_entries[key] != S:  # mover entry changes state
                overlap_count += 1

        print(f"  Total determined entries: {len(required)}")
        print(f"  Mover entries: {len(mover_entries)}")
        print(f"  Mover entries that change state: {overlap_count}")

        # Which entries are used by the shadow?
        result = find_shadow_with_details(cyc, ms, n)
        if result:
            shadow = result['cycle']
            shadow_movers = result['movers']

            shadow_entries_used = set()
            for sidx in range(len(shadow)):
                sc = shadow[sidx]
                sc_next = shadow[(sidx + 1) % len(shadow)]
                diffs = [j for j in range(n) if sc[j] != sc_next[j]]
                if len(diffs) == 1:
                    sm = diffs[0]
                    key = (sm, sc[(sm-1)%n], sc[sm], sc[(sm+1)%n])
                    shadow_entries_used.add(key)

            print(f"  Shadow uses {len(shadow_entries_used)} distinct mover entries")

            # Check: are shadow entries a subset of determined entries?
            all_in = all(key in required for key in shadow_entries_used)
            print(f"  All shadow entries determined: {all_in}")

            # Which processors' entries drive the shadow?
            procs_used = Counter(key[0] for key in shadow_entries_used)
            print(f"  Processors driving shadow: {dict(procs_used)}")

            # Are any BINARY processor entries used?
            bin_entries = {k: v for k, v in required.items()
                         if ms[k[0]] == 2 and v != k[2]}
            print(f"  Binary mover entries (state-changing): {len(bin_entries)}")
            for k, v in sorted(bin_entries.items()):
                print(f"    P{k[0]}({k[1]},{k[2]},{k[3]}) → {v}")


if __name__ == "__main__":
    main()
