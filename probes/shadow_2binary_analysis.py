#!/usr/bin/env python3
"""shadow_2binary_analysis.py — Structural analysis of shadow cycle failure
at the Case 1 boundary: {2,2,3,...,3} with only 2 binary processors.

The shadow cycle theorem requires ≥3 binary. With only 2 binary, the shadow
permutation σ loses degrees of freedom. This script identifies WHICH of the
5 properties fails, what the escape structure looks like, and which
orientations are most promising for witness construction.
"""

from itertools import product as iproduct, combinations
from collections import Counter, defaultdict
import sys


def prod(sc):
    p = 1
    for m in sc:
        p *= m
    return p


def g0(j, n):
    j = j % (2 * n)
    return 1 if 1 <= j <= n else 0


def check_cycle_consistency(cycle_configs, n, ms):
    L = len(cycle_configs)
    required = {}
    for idx in range(L):
        c = cycle_configs[idx]
        c_next = cycle_configs[(idx + 1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, {}, f"non-single mover at step {idx}"
        mover = diffs[0]
        Li = c[(mover - 1) % n]; Si = c[mover]; Ri = c[(mover + 1) % n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return False, {}, f"conflict at f{mover}({Li},{Si},{Ri})"
        required[key] = S_new
        for i in range(n):
            if i != mover:
                Li = c[(i - 1) % n]; Si = c[i]; Ri = c[(i + 1) % n]
                key = (i, Li, Si, Ri)
                if key in required and required[key] != Si:
                    return False, {}, f"conflict"
                required[key] = Si
    return True, required, "OK"


def get_movers(cycle, n):
    movers = []
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        movers.append([k for k in range(n) if c[k] != c_next[k]][0])
    return movers


def construct_sweep_cycle(ms, n, nb_vals):
    """Uniform sweep cycle: procs 0,1,...,n-1 move up then down."""
    config = [0] * n
    cycle = [tuple(config)]
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
    return cycle


def find_all_shadow_cycles(determined, good_set, ms, n, max_steps=200):
    """Find ALL shadow cycles, not just the first one."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    visited_in_any = set()
    cycles_found = []

    for start in non_good:
        if start in visited_in_any:
            continue
        visited = {}
        path = []
        c = start
        valid = True
        for step in range(max_steps):
            if c in good_set:
                # Enters good cycle — this is an ESCAPE!
                valid = False
                break
            if c in visited:
                cycle = path[visited[c]:]
                cycles_found.append(cycle)
                for cfg in cycle:
                    visited_in_any.add(cfg)
                break
            visited[c] = len(path)
            path.append(c)

            # Find forced privileges
            priv = []
            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                key = (i, L, S, R)
                if key in determined and determined[key] != S:
                    priv.append((i, determined[key]))

            if not priv:
                valid = False
                break

            # Try each forced move — prefer staying outside C
            moved = False
            for proc, new_val in priv:
                new_c = list(c)
                new_c[proc] = new_val
                new_c = tuple(new_c)
                if new_c not in good_set:
                    c = new_c
                    moved = True
                    break
            if not moved:
                valid = False
                break

    return cycles_found


def count_determined_entries(determined, ms, n):
    """Count determined vs total entries for each processor."""
    stats = {}
    for i in range(n):
        m_L = ms[(i - 1) % n]
        m_S = ms[i]
        m_R = ms[(i + 1) % n]
        total = m_L * m_S * m_R
        det_count = sum(1 for L in range(m_L) for S in range(m_S) for R in range(m_R)
                        if (i, L, S, R) in determined)
        mover_count = sum(1 for L in range(m_L) for S in range(m_S) for R in range(m_R)
                          if (i, L, S, R) in determined and determined[(i, L, S, R)] != S)
        stats[i] = {
            'total': total,
            'determined': det_count,
            'free': total - det_count,
            'mover_entries': mover_count,
            'stay_entries': det_count - mover_count,
        }
    return stats


def find_escape_configs(determined, good_set, ms, n):
    """Find non-good configs where EVERY forced move enters the good cycle."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    escape_configs = []      # configs where some forced move enters C
    no_forced = []           # configs with no forced privilege at all
    has_escape = []          # configs where forced moves stay outside C

    for c in non_good:
        priv = []
        for i in range(n):
            L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
            key = (i, L, S, R)
            if key in determined and determined[key] != S:
                priv.append((i, determined[key]))

        if not priv:
            no_forced.append(c)
            continue

        all_enter_C = True
        some_enter_C = False
        for proc, new_val in priv:
            new_c = list(c)
            new_c[proc] = new_val
            new_c = tuple(new_c)
            if new_c in good_set:
                some_enter_C = True
            else:
                all_enter_C = False

        if all_enter_C:
            escape_configs.append((c, priv))
        elif some_enter_C:
            has_escape.append((c, priv))

    return escape_configs, no_forced, has_escape


def necklaces_2binary(n):
    """Generate all distinct necklaces for 2 identical binary items in n positions.
    Returns list of state_count tuples."""
    # Place 2 binary procs at positions (i, j) with 0 <= i < j < n
    # Necklace = equivalence class under rotation
    seen = set()
    necklaces = []
    for i in range(n):
        for j in range(i + 1, n):
            # Build ms
            ms = [3] * n
            ms[i] = 2
            ms[j] = 2
            # Canonical form: min rotation
            canonical = None
            for rot in range(n):
                rotated = tuple(ms[(k + rot) % n] for k in range(n))
                if canonical is None or rotated < canonical:
                    canonical = rotated
            if canonical not in seen:
                seen.add(canonical)
                necklaces.append(canonical)
    return sorted(necklaces)


# ═══════════════════════════════════════════════════════════════
# MAIN ANALYSIS
# ═══════════════════════════════════════════════════════════════

def main():
    n = 9
    print("=" * 70)
    print(f"SHADOW CYCLE ANALYSIS: 2-BINARY AT n={n}")
    print(f"Multiset {{2,2,3,3,3,3,3,3,3}}, product = {4 * 3**7} = 4·3^7")
    print("=" * 70)

    # ─── Part 1: Necklace enumeration ───
    print(f"\n{'─' * 60}")
    print("PART 1: NECKLACE ENUMERATION")
    print(f"{'─' * 60}")
    necklaces = necklaces_2binary(n)
    print(f"\nTotal distinct necklaces: {len(necklaces)}")
    for idx, ms in enumerate(necklaces):
        bin_pos = [i for i in range(n) if ms[i] == 2]
        sep = min((bin_pos[1] - bin_pos[0]) % n, (bin_pos[0] - bin_pos[1]) % n)
        print(f"  [{idx+1}] {ms}  bin_pos={bin_pos}  separation={sep}")

    # ─── Part 2: Comparison with 3-binary ───
    print(f"\n{'─' * 60}")
    print("PART 2: DETERMINED ENTRY COMPARISON (2-binary vs 3-binary)")
    print(f"{'─' * 60}")

    # 3-binary reference: ms = (2,2,2,3,3,3,3,3,3) at n=9
    ms_3bin = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    nb_vals_3bin = {i: 1 for i in range(n)}
    cycle_3bin = construct_sweep_cycle(list(ms_3bin), n, nb_vals_3bin)
    if cycle_3bin:
        ok, det_3bin, msg = check_cycle_consistency(cycle_3bin, n, list(ms_3bin))
        stats_3bin = count_determined_entries(det_3bin, list(ms_3bin), n)
        print(f"\n3-binary ms={ms_3bin}, cycle_len={len(cycle_3bin)}")
        total_det_3 = sum(s['determined'] for s in stats_3bin.values())
        total_all_3 = sum(s['total'] for s in stats_3bin.values())
        total_free_3 = total_all_3 - total_det_3
        for i in range(n):
            s = stats_3bin[i]
            print(f"  P{i}(m={ms_3bin[i]}): {s['determined']}/{s['total']} det "
                  f"({s['mover_entries']} mover, {s['stay_entries']} stay, {s['free']} free)")
        print(f"  TOTAL: {total_det_3}/{total_all_3} determined, {total_free_3} free "
              f"({100*total_det_3/total_all_3:.1f}%)")

    # 2-binary: test adjacent (2,2,3,3,3,3,3,3,3) and separated (2,3,3,3,3,2,3,3,3)
    test_ms = [
        (2, 2, 3, 3, 3, 3, 3, 3, 3),  # adjacent
        (2, 3, 2, 3, 3, 3, 3, 3, 3),  # sep=2
        (2, 3, 3, 3, 2, 3, 3, 3, 3),  # sep=4
    ]

    for ms in test_ms:
        ms_list = list(ms)
        nb_vals = {i: 1 for i in range(n)}
        cycle = construct_sweep_cycle(ms_list, n, nb_vals)
        if cycle is None:
            print(f"\n  ms={ms}: NO VALID SWEEP CYCLE")
            continue
        ok, det, msg = check_cycle_consistency(cycle, n, ms_list)
        if not ok:
            print(f"\n  ms={ms}: INCONSISTENT — {msg}")
            continue
        stats = count_determined_entries(det, ms_list, n)
        bin_pos = [i for i in range(n) if ms[i] == 2]
        total_det = sum(s['determined'] for s in stats.values())
        total_all = sum(s['total'] for s in stats.values())
        total_free = total_all - total_det
        print(f"\n2-binary ms={ms}, bin_pos={bin_pos}, cycle_len={len(cycle)}")
        for i in range(n):
            s = stats[i]
            marker = " ◄ BINARY" if ms[i] == 2 else ""
            print(f"  P{i}(m={ms[i]}): {s['determined']}/{s['total']} det "
                  f"({s['mover_entries']} mover, {s['stay_entries']} stay, {s['free']} free){marker}")
        print(f"  TOTAL: {total_det}/{total_all} determined, {total_free} free "
              f"({100*total_det/total_all:.1f}%)")

    # ─── Part 3: Shadow property analysis ───
    print(f"\n{'─' * 60}")
    print("PART 3: SHADOW PROPERTY ANALYSIS")
    print(f"{'─' * 60}")

    for ms in test_ms:
        ms_list = list(ms)
        bin_pos = [i for i in range(n) if ms[i] == 2]
        nb_procs = [i for i in range(n) if ms[i] > 2]
        nb_vals = {i: 1 for i in range(n)}
        cycle = construct_sweep_cycle(ms_list, n, nb_vals)
        if cycle is None:
            continue
        ok, det, msg = check_cycle_consistency(cycle, n, ms_list)
        if not ok:
            continue

        good_set = set(cycle)
        good_movers = get_movers(cycle, n)

        # Build mover entry lookup
        mover_entries = set()
        for gi in range(len(cycle)):
            gm = good_movers[gi]
            gc = cycle[gi]
            gL = gc[(gm - 1) % n]; gS = gc[gm]; gR = gc[(gm + 1) % n]
            mover_entries.add((gm, gL, gS, gR))

        print(f"\nms={ms}, bin_pos={bin_pos}")
        print(f"Good cycle length: {len(cycle)}, good configs: {len(good_set)}")
        print(f"Total configs: {prod(ms_list)}")

        # Find escape configs
        esc_all, no_forced, esc_some = find_escape_configs(det, good_set, ms_list, n)
        print(f"\nEscape analysis:")
        print(f"  Non-good configs with NO forced privilege: {len(no_forced)}")
        print(f"  Non-good configs where SOME forced move → C: {len(esc_some)}")
        print(f"  Non-good configs where ALL forced moves → C: {len(esc_all)}")

        if esc_all:
            print(f"\n  *** ESCAPE CONFIGS (all forced moves enter C): ***")
            for c, priv in esc_all[:10]:
                priv_str = ", ".join(f"P{p}→{v}" for p, v in priv)
                print(f"    {c}  priv=[{priv_str}]")
                for p, v in priv:
                    new_c = list(c)
                    new_c[p] = v
                    new_c_t = tuple(new_c)
                    if new_c_t in good_set:
                        gi = list(cycle).index(new_c_t)
                        gm = good_movers[gi]
                        print(f"      → {new_c_t} = good[{gi}], mover=P{gm}")
            if len(esc_all) > 10:
                print(f"    ... and {len(esc_all) - 10} more")

        # Find shadow cycles
        shadow_cycles = find_all_shadow_cycles(det, good_set, ms_list, n)
        print(f"\nShadow cycles found: {len(shadow_cycles)}")
        total_shadow_configs = sum(len(sc) for sc in shadow_cycles)
        non_good_count = prod(ms_list) - len(good_set)
        print(f"  Total shadow-cycle configs: {total_shadow_configs}")
        print(f"  Non-good configs: {non_good_count}")
        print(f"  Configs NOT in shadow cycles: {non_good_count - total_shadow_configs}")

        # Check shadow properties for each cycle
        for si, shadow in enumerate(shadow_cycles[:5]):
            print(f"\n  Shadow cycle #{si+1}: length={len(shadow)}")

            # (i) Closure: is it a proper cycle?
            is_cycle = len(set(shadow)) == len(shadow)
            print(f"    (i)   Closure (proper cycle): {is_cycle}")

            # (ii) Disjoint from C?
            disjoint = all(s not in good_set for s in shadow)
            print(f"    (ii)  Disjoint from C: {disjoint}")

            # (iii) All entries determined?
            # (v)  Uses mover entries?
            all_det = True
            all_mover = True
            shadow_movers = []
            for idx in range(len(shadow)):
                sc = shadow[idx]
                sc_next = shadow[(idx + 1) % len(shadow)]
                diffs = [k for k in range(n) if sc[k] != sc_next[k]]
                if len(diffs) != 1:
                    all_det = False
                    shadow_movers.append(-1)
                    continue
                sm = diffs[0]
                shadow_movers.append(sm)
                sL = sc[(sm - 1) % n]; sS = sc[sm]; sR = sc[(sm + 1) % n]
                key = (sm, sL, sS, sR)
                if key not in det:
                    all_det = False
                if key not in mover_entries:
                    all_mover = False

            print(f"    (iii) All entries determined: {all_det}")
            print(f"    (v)   All mover entries: {all_mover}")

            # (iv) Same length as C?
            same_len = len(shadow) == len(cycle)
            print(f"    (iv)  Same length as C ({len(cycle)}): {same_len}")

            # Mover sequence
            print(f"    Good movers:   {good_movers}")
            print(f"    Shadow movers: {shadow_movers}")

            # Binary state analysis
            good_bin = [tuple(cycle[t][p] for p in bin_pos) for t in range(len(cycle))]
            shadow_bin = [tuple(shadow[t][p] for p in bin_pos) for t in range(len(shadow))]
            print(f"    Good binary states:   {sorted(set(good_bin))}")
            print(f"    Shadow binary states: {sorted(set(shadow_bin))}")

        if len(shadow_cycles) > 5:
            print(f"\n  ... and {len(shadow_cycles) - 5} more shadow cycles")

    # ─── Part 4: Critical comparison — 2 vs 3 binary ───
    print(f"\n{'─' * 60}")
    print("PART 4: WHAT BREAKS WITH 2 BINARY")
    print(f"{'─' * 60}")

    # With 3 binary: binary procs have ALL entries determined (2 states → full determination)
    # With 2 binary: still fully determined, but we have 2 fewer binary procs
    # So the total determined fraction drops

    # Key: with 3 binary, the shadow cycle uses binary flips. Each step
    # changes exactly one proc. With only 2 binary, there aren't enough
    # binary flips to drive a full-length shadow cycle.

    ms_adj = (2, 2, 3, 3, 3, 3, 3, 3, 3)
    nb_vals_adj = {i: 1 for i in range(n)}
    cycle_adj = construct_sweep_cycle(list(ms_adj), n, nb_vals_adj)
    if cycle_adj:
        ok, det_adj, msg = check_cycle_consistency(cycle_adj, n, list(ms_adj))
        good_set_adj = set(cycle_adj)
        good_movers_adj = get_movers(cycle_adj, n)

        print(f"\nms={ms_adj}")
        print(f"Good cycle has {len(cycle_adj)} steps, movers = {good_movers_adj}")

        # For each non-good config, trace where forced moves lead
        all_configs = list(iproduct(*[range(m) for m in ms_adj]))
        non_good = [c for c in all_configs if c not in good_set_adj]

        # Categorize: can daemon be trapped in a shadow, or can it escape?
        trapped_configs = set()
        escapable_configs = set()
        undetermined_configs = set()

        for c in non_good:
            priv = []
            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                key = (i, L, S, R)
                if key in det_adj and det_adj[key] != S:
                    priv.append((i, det_adj[key]))

            if not priv:
                undetermined_configs.add(c)
                continue

            has_out = False
            has_in = False
            for p, v in priv:
                new_c = list(c)
                new_c[p] = v
                new_c_t = tuple(new_c)
                if new_c_t in good_set_adj:
                    has_in = True
                else:
                    has_out = True

            if has_out:
                trapped_configs.add(c)  # daemon can choose to stay outside
            else:
                escapable_configs.add(c)  # all forced moves enter C

        print(f"\nNon-good config classification:")
        print(f"  Total non-good: {len(non_good)}")
        print(f"  With forced privilege, can stay outside C: {len(trapped_configs)}")
        print(f"  With forced privilege, ALL moves enter C: {len(escapable_configs)}")
        print(f"  No forced privilege (free entries): {len(undetermined_configs)}")
        print(f"  Fraction undetermined: {len(undetermined_configs)}/{len(non_good)} "
              f"= {100*len(undetermined_configs)/len(non_good):.1f}%")

        print(f"\n*** KEY INSIGHT ***")
        print(f"With 3 binary: ALL non-good configs have forced privilege (0 undetermined)")
        print(f"With 2 binary: {len(undetermined_configs)} configs have NO forced privilege")
        print(f"These {len(undetermined_configs)} configs are WHERE THE ESCAPE LIVES:")
        print(f"The daemon can reach these configs, and then ANY move is possible")
        print(f"(free entries can be set to point back to the good cycle)")

    # ─── Part 5: Escape route structure ───
    print(f"\n{'─' * 60}")
    print("PART 5: ESCAPE ROUTE STRUCTURE")
    print(f"{'─' * 60}")

    if cycle_adj:
        ok, det_adj, msg = check_cycle_consistency(cycle_adj, n, list(ms_adj))
        good_set_adj = set(cycle_adj)

        # Sample some undetermined configs and analyze their structure
        undet_list = sorted(undetermined_configs)
        print(f"\nSample undetermined configs (first 20):")
        for c in undet_list[:20]:
            bin_state = tuple(c[i] for i in range(n) if ms_adj[i] == 2)
            nb_state = tuple(c[i] for i in range(n) if ms_adj[i] == 3)

            # Check which procs have ANY determined entry
            det_procs = []
            free_procs = []
            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                key = (i, L, S, R)
                if key in det_adj:
                    det_procs.append(f"P{i}={det_adj[key]}")
                else:
                    free_procs.append(f"P{i}")
            print(f"  {c}  bin={bin_state}  free={free_procs}")

        # What's the binary state distribution of undetermined configs?
        bin_states_undet = Counter()
        for c in undetermined_configs:
            bin_state = tuple(c[i] for i in range(n) if ms_adj[i] == 2)
            bin_states_undet[bin_state] += 1
        print(f"\nBinary state distribution of undetermined configs:")
        for bs, count in sorted(bin_states_undet.items()):
            in_good = any(tuple(gc[i] for i in range(n) if ms_adj[i] == 2) == bs
                          for gc in good_set_adj)
            print(f"  bin={bs}: {count} configs  (in good cycle: {in_good})")

    # ─── Part 6: All necklaces — shadow length comparison ───
    print(f"\n{'─' * 60}")
    print("PART 6: SHADOW CYCLES ACROSS ALL NECKLACES")
    print(f"{'─' * 60}")

    for ms in necklaces:
        ms_list = list(ms)
        bin_pos = [i for i in range(n) if ms[i] == 2]
        sep = min((bin_pos[1] - bin_pos[0]) % n, (bin_pos[0] - bin_pos[1]) % n)
        nb_vals = {i: 1 for i in range(n)}
        cycle = construct_sweep_cycle(ms_list, n, nb_vals)
        if cycle is None:
            print(f"  ms={ms} sep={sep}: NO SWEEP CYCLE")
            continue
        ok, det, msg = check_cycle_consistency(cycle, n, ms_list)
        if not ok:
            print(f"  ms={ms} sep={sep}: INCONSISTENT")
            continue

        good_set = set(cycle)
        total = prod(ms_list)

        # Count undetermined
        all_configs = list(iproduct(*[range(m) for m in ms]))
        non_good = [c for c in all_configs if c not in good_set]
        n_undet = 0
        n_esc_all = 0
        for c in non_good:
            priv = []
            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                key = (i, L, S, R)
                if key in det and det[key] != S:
                    priv.append((i, det[key]))
            if not priv:
                n_undet += 1
            else:
                all_enter = all(
                    tuple(list(c[:p]) + [v] + list(c[p+1:])) in good_set
                    for p, v in priv
                )
                if all_enter:
                    n_esc_all += 1

        shadow_cycles = find_all_shadow_cycles(det, good_set, ms_list, n)
        shadow_lens = [len(sc) for sc in shadow_cycles]
        total_shadow = sum(shadow_lens)

        print(f"  ms={ms} sep={sep}: "
              f"undet={n_undet}/{len(non_good)} "
              f"esc_all={n_esc_all} "
              f"shadows={len(shadow_cycles)} lens={sorted(shadow_lens) if shadow_lens else '[]'} "
              f"total_shadow={total_shadow}")

    # ─── Part 7: Comparison with n=8 witness structure ───
    print(f"\n{'─' * 60}")
    print("PART 7: n=5..8 WITNESS ANALYSIS — BINARY POSITION PATTERNS")
    print(f"{'─' * 60}")

    witnesses = {
        5: (2, 2, 2, 3, 4),
        6: (2, 2, 2, 4, 3, 3),
        7: (3, 2, 2, 2, 3, 4, 3),
        8: (2, 2, 3, 4, 3, 3, 2, 3),
    }
    for wn, wms in witnesses.items():
        bin_pos = [i for i in range(wn) if wms[i] == 2]
        quat_pos = [i for i in range(wn) if wms[i] == 4]
        tern_pos = [i for i in range(wn) if wms[i] == 3]
        n_bin = len(bin_pos)
        print(f"  n={wn}: ms={wms}, product={prod(wms)}")
        print(f"    binary@{bin_pos}, ternary@{tern_pos}, quaternary@{quat_pos}")
        print(f"    #binary={n_bin}, formula=32·3^{wn-4}={32*(3**(wn-4))}")


if __name__ == "__main__":
    main()
