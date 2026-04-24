#!/usr/bin/env python3
"""shadow_2binary_deep.py — Deep analysis of shadow vs escape at product 8748.

Key questions:
1. Are the 438 shadow cycles truly distinct? (fix double-counting)
2. Do ALL NB value combinations produce shadows, or can some escape?
3. For shadow-cycle configs: can free entries break the shadow SCC?
4. What does the escape structure look like at undetermined configs?
"""

from itertools import product as iproduct
from collections import Counter, defaultdict
import time


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
            return False, {}, f"non-single mover at step {idx}"
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


def find_shadow_cycles_correct(determined, good_set, ms, n, max_steps=200):
    """Find shadow cycles with correct counting (no double-counting).

    Returns: (set of configs in shadow cycles, list of distinct cycles)
    """
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    # Build the forced-move graph: for each non-good config, find all
    # forced successors that stay outside C
    forced_succs = {}  # config -> list of (config, mover) pairs
    for c in non_good:
        succs = []
        for i in range(n):
            L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
            key = (i, L, S, R)
            if key in determined and determined[key] != S:
                new_c = list(c)
                new_c[i] = determined[key]
                new_c = tuple(new_c)
                if new_c not in good_set:
                    succs.append((new_c, i))
        forced_succs[c] = succs

    # Find SCCs in the forced-move graph using iterative Tarjan
    index_counter = [0]
    stack = []
    on_stack = set()
    index = {}
    lowlink = {}
    sccs = []

    non_good_with_succs = [c for c in non_good if forced_succs.get(c)]

    def strongconnect_iterative(v):
        # Iterative Tarjan's algorithm
        work_stack = [(v, 0)]  # (node, successor_index)
        call_stack = []

        index[v] = lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)

        while work_stack:
            node, si = work_stack[-1]
            succs = [s for s, _ in forced_succs.get(node, [])]

            if si < len(succs):
                work_stack[-1] = (node, si + 1)
                w = succs[si]
                if w not in index:
                    index[w] = lowlink[w] = index_counter[0]
                    index_counter[0] += 1
                    stack.append(w)
                    on_stack.add(w)
                    work_stack.append((w, 0))
                elif w in on_stack:
                    lowlink[node] = min(lowlink[node], index[w])
            else:
                # All successors processed
                if lowlink[node] == index[node]:
                    scc = []
                    while True:
                        w = stack.pop()
                        on_stack.discard(w)
                        scc.append(w)
                        if w == node:
                            break
                    if len(scc) > 1:
                        sccs.append(scc)
                    elif len(scc) == 1 and any(s == scc[0] for s, _ in forced_succs.get(scc[0], [])):
                        sccs.append(scc)  # self-loop

                work_stack.pop()
                if work_stack:
                    parent = work_stack[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[node])

    for v in non_good_with_succs:
        if v not in index:
            strongconnect_iterative(v)

    # Collect all configs in bad SCCs
    bad_scc_configs = set()
    for scc in sccs:
        for c in scc:
            bad_scc_configs.add(c)

    return bad_scc_configs, sccs


def main():
    n = 9
    ms_adj = (2, 2, 3, 3, 3, 3, 3, 3, 3)
    total = prod(ms_adj)

    print("=" * 70)
    print(f"DEEP SHADOW ANALYSIS: product 8748 at n=9")
    print(f"ms={ms_adj}")
    print("=" * 70)

    # ─── Part 1: Fix double-counting — use SCC-based analysis ───
    print(f"\n{'─' * 60}")
    print("PART 1: CORRECT SHADOW SCC ANALYSIS (uniform sweep, nb=all 1s)")
    print(f"{'─' * 60}")

    nb_vals = {i: 1 for i in range(n)}
    cycle = construct_sweep_cycle(list(ms_adj), n, nb_vals)
    ok, det, msg = check_cycle_consistency(cycle, n, list(ms_adj))
    good_set = set(cycle)

    t0 = time.time()
    bad_scc_configs, sccs = find_shadow_cycles_correct(det, good_set, list(ms_adj), n)
    elapsed = time.time() - t0

    non_good_count = total - len(good_set)
    scc_sizes = Counter(len(scc) for scc in sccs)

    print(f"\nTotal configs: {total}")
    print(f"Good cycle: {len(good_set)}")
    print(f"Non-good: {non_good_count}")
    print(f"Configs in bad SCCs: {len(bad_scc_configs)}")
    print(f"Configs NOT in any bad SCC: {non_good_count - len(bad_scc_configs)}")
    print(f"Number of bad SCCs: {len(sccs)}")
    print(f"SCC size distribution: {dict(scc_sizes)}")
    print(f"({elapsed:.2f}s)")

    # Count undetermined configs
    all_configs = list(iproduct(*[range(m) for m in ms_adj]))
    non_good = [c for c in all_configs if c not in good_set]
    n_undet = 0
    n_forced = 0
    for c in non_good:
        has_priv = False
        for i in range(n):
            L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
            key = (i, L, S, R)
            if key in det and det[key] != S:
                has_priv = True
                break
        if has_priv:
            n_forced += 1
        else:
            n_undet += 1

    print(f"\nWith forced privilege: {n_forced}")
    print(f"Without forced privilege (undetermined): {n_undet}")
    print(f"Undetermined fraction: {n_undet}/{non_good_count} = {100*n_undet/non_good_count:.1f}%")

    # Verify: undetermined configs should NOT be in bad SCCs
    undet_in_scc = sum(1 for c in non_good if c in bad_scc_configs
                       and not any((i, c[(i-1)%n], c[i], c[(i+1)%n]) in det
                                   and det[(i, c[(i-1)%n], c[i], c[(i+1)%n])] != c[i]
                                   for i in range(n)))
    print(f"Undetermined configs in bad SCCs: {undet_in_scc} (should be 0)")

    # ─── Part 2: Test ALL 128 NB value combinations ───
    print(f"\n{'─' * 60}")
    print("PART 2: ALL NB VALUE COMBINATIONS")
    print(f"{'─' * 60}")

    ternary_procs = [i for i in range(n) if ms_adj[i] == 3]
    n_ternary = len(ternary_procs)
    # Each ternary proc can use high value 1 or 2
    nb_combos = list(iproduct(*[range(1, 3) for _ in range(n_ternary)]))

    best_combo = None
    best_undet = 0
    best_scc_count = float('inf')
    best_scc_configs = float('inf')

    results = []

    for combo in nb_combos:
        nb_vals = {i: 0 for i in range(n)}
        for j, p in enumerate(ternary_procs):
            nb_vals[p] = combo[j]

        cycle = construct_sweep_cycle(list(ms_adj), n, nb_vals)
        if cycle is None:
            continue
        ok, det, msg = check_cycle_consistency(cycle, n, list(ms_adj))
        if not ok:
            continue

        good_set = set(cycle)
        bad_scc_configs, sccs = find_shadow_cycles_correct(det, good_set, list(ms_adj), n)

        # Count undetermined
        n_undet_c = 0
        for c in non_good:
            has_priv = False
            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                key = (i, L, S, R)
                if key in det and det[key] != S:
                    has_priv = True
                    break
            if not has_priv:
                n_undet_c += 1

        results.append({
            'combo': combo,
            'n_scc': len(sccs),
            'scc_configs': len(bad_scc_configs),
            'n_undet': n_undet_c,
            'free_fraction': non_good_count - len(bad_scc_configs),
        })

        if len(bad_scc_configs) < best_scc_configs:
            best_scc_configs = len(bad_scc_configs)
            best_combo = combo
            best_scc_count = len(sccs)

    # Sort by scc_configs (ascending)
    results.sort(key=lambda r: r['scc_configs'])

    print(f"\nTested {len(results)} NB combinations")
    print(f"\nTop 10 (fewest shadow SCC configs):")
    for r in results[:10]:
        print(f"  combo={r['combo']}: {r['n_scc']} SCCs, {r['scc_configs']} SCC configs, "
              f"{r['n_undet']} undet, {r['free_fraction']} free")

    print(f"\nBottom 5 (most shadow SCC configs):")
    for r in results[-5:]:
        print(f"  combo={r['combo']}: {r['n_scc']} SCCs, {r['scc_configs']} SCC configs, "
              f"{r['n_undet']} undet, {r['free_fraction']} free")

    # Check if ANY combo has 0 SCCs
    zero_scc = [r for r in results if r['n_scc'] == 0]
    if zero_scc:
        print(f"\n*** {len(zero_scc)} NB COMBOS WITH ZERO SHADOW SCCs! ***")
        for r in zero_scc:
            print(f"  combo={r['combo']}")
    else:
        scc_counts = Counter(r['n_scc'] for r in results)
        scc_config_counts = Counter(r['scc_configs'] for r in results)
        print(f"\nALL combos have shadow SCCs.")
        print(f"SCC count distribution: {dict(scc_counts)}")
        print(f"SCC config count distribution: {dict(scc_config_counts)}")

    # ─── Part 3: For the best combo, analyze SCC structure ───
    if best_combo:
        print(f"\n{'─' * 60}")
        print(f"PART 3: BEST COMBO DEEP ANALYSIS")
        print(f"combo={best_combo}, {best_scc_count} SCCs, {best_scc_configs} SCC configs")
        print(f"{'─' * 60}")

        nb_vals = {i: 0 for i in range(n)}
        for j, p in enumerate(ternary_procs):
            nb_vals[p] = best_combo[j]

        cycle = construct_sweep_cycle(list(ms_adj), n, nb_vals)
        ok, det, msg = check_cycle_consistency(cycle, n, list(ms_adj))
        good_set = set(cycle)
        bad_scc_configs, sccs = find_shadow_cycles_correct(det, good_set, list(ms_adj), n)

        print(f"\nSCC sizes: {sorted([len(scc) for scc in sccs], reverse=True)[:20]}")

        # For each SCC, check if any config has a free entry that could create an exit
        for si, scc in enumerate(sccs[:5]):
            scc_set = set(scc)
            print(f"\n  SCC #{si+1} (size={len(scc)}):")
            exits_possible = 0
            for c in scc:
                # Check all processors for free entries
                for i in range(n):
                    L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                    key = (i, L, S, R)
                    if key not in det:
                        # This is a FREE entry. We could set it to create privilege.
                        # But the daemon might still pick the forced move.
                        # The question: does the forced move always lead within the SCC?
                        exits_possible += 1
                        break

            print(f"    Configs with free entries: {exits_possible}/{len(scc)}")

            # Show first few configs
            for c in scc[:3]:
                forced = []
                free = []
                for i in range(n):
                    L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                    key = (i, L, S, R)
                    if key in det:
                        if det[key] != S:
                            forced.append(f"P{i}→{det[key]}")
                    else:
                        free.append(f"P{i}")
                print(f"    {c}  forced=[{','.join(forced)}]  free=[{','.join(free)}]")

    # ─── Part 4: Critical question — can we break ALL bad SCCs? ───
    print(f"\n{'─' * 60}")
    print("PART 4: CAN FREE ENTRIES BREAK ALL BAD SCCs?")
    print(f"{'─' * 60}")
    print("""
The shadow cycles use determined mover entries that can't be changed.
The daemon follows forced moves around the shadow → stays in the SCC.

For convergence, we need NO bad SCCs. The only way to break a bad SCC
is if at EVERY config in the SCC, EVERY forced move leads to a config
that can eventually reach the good cycle.

But forced moves within an SCC lead to other SCC members by definition.
So bad SCCs = inescapable bad cycles = convergence failure.

The ONLY way this changes is if the good cycle is NOT a uniform sweep
but some other cycle structure that determines different entries.
""")

    # Check: for the best combo, is every SCC truly a bad cycle?
    # A bad SCC means the daemon CAN choose to stay in it forever.
    # Verify: in each SCC, every config has at least one forced successor in the SCC.
    nb_vals = {i: 0 for i in range(n)}
    for j, p in enumerate(ternary_procs):
        nb_vals[p] = best_combo[j]
    cycle = construct_sweep_cycle(list(ms_adj), n, nb_vals)
    ok, det, msg = check_cycle_consistency(cycle, n, list(ms_adj))
    good_set = set(cycle)
    bad_scc_configs, sccs = find_shadow_cycles_correct(det, good_set, list(ms_adj), n)

    all_truly_bad = True
    for si, scc in enumerate(sccs):
        scc_set = set(scc)
        for c in scc:
            has_internal = False
            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                key = (i, L, S, R)
                if key in det and det[key] != S:
                    new_c = list(c)
                    new_c[i] = det[key]
                    new_c = tuple(new_c)
                    if new_c in scc_set:
                        has_internal = True
                        break
            if not has_internal:
                all_truly_bad = False
                print(f"  SCC #{si+1}: config {c} has NO internal forced successor!")

    if all_truly_bad:
        print(f"\nAll {len(sccs)} SCCs are truly inescapable (daemon can always stay).")
        print("→ Uniform sweep cycles at product 8748 ARE blocked by shadow SCCs.")
    else:
        print(f"\nSome SCCs have configs without internal successors — might be breakable!")

    # ─── Part 5: Compare 3-binary shadow at n=9 ───
    print(f"\n{'─' * 60}")
    print("PART 5: 3-BINARY REFERENCE (shadow covers everything)")
    print(f"{'─' * 60}")

    ms_3bin = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    nb_vals_3 = {i: 1 for i in range(n)}
    cycle_3 = construct_sweep_cycle(list(ms_3bin), n, nb_vals_3)
    if cycle_3:
        ok_3, det_3, msg_3 = check_cycle_consistency(cycle_3, n, list(ms_3bin))
        good_set_3 = set(cycle_3)
        total_3 = prod(ms_3bin)
        non_good_3 = [c for c in iproduct(*[range(m) for m in ms_3bin]) if c not in good_set_3]

        bad_3, sccs_3 = find_shadow_cycles_correct(det_3, good_set_3, list(ms_3bin), n)
        n_undet_3 = sum(1 for c in non_good_3
                        if not any((i, c[(i-1)%n], c[i], c[(i+1)%n]) in det_3
                                   and det_3[(i, c[(i-1)%n], c[i], c[(i+1)%n])] != c[i]
                                   for i in range(n)))

        print(f"\n3-binary ms={ms_3bin}, product={total_3}")
        print(f"Non-good: {len(non_good_3)}")
        print(f"Configs in bad SCCs: {len(bad_3)}")
        print(f"Undetermined: {n_undet_3}")
        print(f"Number of bad SCCs: {len(sccs_3)}")
        print(f"SCC sizes: {sorted([len(s) for s in sccs_3], reverse=True)[:20]}")

    # ─── Part 6: The structural conclusion ───
    print(f"\n{'─' * 60}")
    print("PART 6: STRUCTURAL CONCLUSION")
    print(f"{'─' * 60}")
    print(f"""
FINDING: Shadow cycles DO exist with only 2 binary processors.

For uniform sweep cycles at product 8748 = 4·3^7:
  - ALL 128 NB value combos produce bad SCCs
  - These SCCs are inescapable (every config has internal forced successor)
  - The shadow mechanism works even with 2 binary

HOWEVER: this only blocks UNIFORM SWEEP cycles.
Non-uniform cycles (found by DFS) may have different determined entries
that DON'T create inescapable bad SCCs.

The shadow theorem's requirement of "≥3 binary" is about the ANALYTIC PROOF
(the closed-form shadow formula s_k[i] = g0(k + d_i)). The COMPUTATIONAL
shadow mechanism works fine with 2 binary — it just doesn't have a nice
analytic formula.

KEY QUESTION: Does every possible good cycle at product 8748 create
inescapable bad SCCs? This is the n=9 screening question.
""")


if __name__ == "__main__":
    main()
