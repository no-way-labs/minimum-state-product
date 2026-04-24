#!/usr/bin/env python3
"""scc_invariance_test.py — Why are the 3 SCCs of [252, 168, 72] invariant?

Key question: Are the same 492 CONFIGS in the SCCs across different products,
or are they different configs that happen to form same-sized SCCs?

Also test: what happens with all-ternary (3^9 = 19683)?
"""

from itertools import product as cartesian
from collections import Counter


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
        Li = c[(mover - 1) % n]; Si = c[mover]; Ri = c[(mover + 1) % n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return False, {}
        required[key] = S_new
        for i in range(n):
            if i != mover:
                Li = c[(i - 1) % n]; Si = c[i]; Ri = c[(i + 1) % n]
                key = (i, Li, Si, Ri)
                if key in required and required[key] != Si:
                    return False, {}
                required[key] = Si
    return True, required


def find_sccs(forced_succs):
    """Iterative Tarjan SCC."""
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

    return sccs


def get_sccs_for_ms(ms):
    n = len(ms)
    ms_list = list(ms)
    nb_vals = {i: 1 for i in range(n)}
    cycle = construct_sweep_cycle(ms_list, n, nb_vals)
    if not cycle:
        return None, None, None
    ok, det = check_cycle_consistency(cycle, n, ms_list)
    if not ok:
        return None, None, None
    good_set = set(cycle)
    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    forced_succs = {}
    for c in non_good:
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

    sccs = find_sccs(forced_succs)
    return sccs, det, cycle


def main():
    n = 9
    print("=" * 70)
    print("SCC INVARIANCE ANALYSIS")
    print("=" * 70)

    # Test 1: Are the actual 492 configs the SAME across different multisets?
    print("\n--- TEST 1: Config identity across multisets ---")
    test_cases = [
        (2, 2, 3, 3, 3, 3, 3, 3, 3),   # product 8748
        (2, 3, 2, 3, 3, 3, 3, 3, 3),   # product 8748, different orientation
        (2, 3, 3, 3, 3, 3, 3, 3, 3),   # product 13122
        (2, 2, 3, 3, 3, 3, 3, 3, 4),   # product 11664
        (2, 3, 3, 3, 3, 3, 3, 3, 4),   # product 17496
    ]

    scc_sets = {}
    for ms in test_cases:
        sccs, det, cycle = get_sccs_for_ms(ms)
        if sccs is None:
            print(f"  {ms}: NO CYCLE")
            continue
        sizes = sorted([len(s) for s in sccs], reverse=True)
        scc_configs = set()
        for scc in sccs:
            scc_configs.update(scc)
        scc_sets[ms] = scc_configs
        print(f"  {ms}: product={prod(ms)}, SCCs={sizes}, total={len(scc_configs)}")

    # Compare config sets
    ref_ms = test_cases[0]
    ref_set = scc_sets.get(ref_ms, set())
    for ms in test_cases[1:]:
        if ms in scc_sets:
            other = scc_sets[ms]
            overlap = ref_set & other
            only_ref = ref_set - other
            only_other = other - ref_set
            print(f"  {ref_ms} vs {ms}:")
            print(f"    overlap={len(overlap)}, only_ref={len(only_ref)}, only_other={len(only_other)}")

    # Test 2: All-ternary case (3^9 = 19683)
    print("\n--- TEST 2: All-ternary (3^9) ---")
    ms_all3 = (3,) * 9
    # For all-ternary, sweep cycle goes 0→1 for each proc, then back
    # But with NB=1 for all: 0→1→0 cycle
    sccs_all3, det_all3, cycle_all3 = get_sccs_for_ms(ms_all3)
    if sccs_all3 is not None:
        sizes = sorted([len(s) for s in sccs_all3], reverse=True)
        total_scc = sum(sizes)
        print(f"  ms={ms_all3}: SCCs={sizes}, total={total_scc}")
        print(f"  Cycle length: {len(cycle_all3)}")
        print(f"  Total configs: {prod(ms_all3)}")
        print(f"  Good configs: {len(set(cycle_all3))}")
        print(f"  Non-good: {prod(ms_all3) - len(set(cycle_all3))}")
    else:
        print(f"  ms={ms_all3}: NO SWEEP CYCLE")

    # Also try NB=2 for all-ternary
    print("\n  Trying NB=2 for all-ternary...")
    ms_list = list(ms_all3)
    nb_vals = {i: 2 for i in range(n)}
    cycle_nb2 = construct_sweep_cycle(ms_list, n, nb_vals)
    if cycle_nb2:
        ok, det_nb2 = check_cycle_consistency(cycle_nb2, n, ms_list)
        if ok:
            good_set = set(cycle_nb2)
            all_configs = list(cartesian(*(range(m) for m in ms_all3)))
            non_good = [c for c in all_configs if c not in good_set]
            non_good_set = set(non_good)
            forced_succs = {}
            for c in non_good:
                succs = []
                for i in range(n):
                    L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                    key = (i, L, S, R)
                    if key in det_nb2 and det_nb2[key] != S:
                        new_c = list(c)
                        new_c[i] = det_nb2[key]
                        new_c = tuple(new_c)
                        if new_c in non_good_set:
                            succs.append(new_c)
                if succs:
                    forced_succs[c] = succs
            sccs_nb2 = find_sccs(forced_succs)
            sizes = sorted([len(s) for s in sccs_nb2], reverse=True)
            print(f"    NB=2 sweep: SCCs={sizes}, total={sum(sizes)}")
            print(f"    Cycle length: {len(cycle_nb2)}")
        else:
            print(f"    NB=2 sweep: consistency FAIL")
    else:
        print(f"    NB=2 sweep: no cycle")

    # Test 3: What about the determined entries?
    # Are the det entries creating the SCCs identical across multisets?
    print("\n--- TEST 3: Determined entry analysis ---")
    ms_a = (2, 2, 3, 3, 3, 3, 3, 3, 3)
    ms_b = (2, 3, 3, 3, 3, 3, 3, 3, 3)
    ms_c = (3, 3, 3, 3, 3, 3, 3, 3, 3)

    for ms in [ms_a, ms_b, ms_c]:
        sccs, det, cycle = get_sccs_for_ms(ms)
        if det is None:
            print(f"  {ms}: no det")
            continue
        n_det = len(det)
        # Count how many det entries force a state change
        n_forcing = sum(1 for (i, L, S, R), v in det.items() if v != S)
        # Total possible (i, L, S, R) tuples
        total_possible = sum(ms[(i-1)%n] * ms[i] * ms[(i+1)%n] for i in range(n))
        print(f"  {ms}: det_entries={n_det}/{total_possible} ({100*n_det/total_possible:.1f}%), "
              f"forcing={n_forcing}")

    # Test 4: Check if the 492 configs are "universal" — do they exist in all state spaces?
    print("\n--- TEST 4: Config universality ---")
    # Take the 492 configs from ms=(2,2,3,3,3,3,3,3,3)
    sccs_ref, _, _ = get_sccs_for_ms((2, 2, 3, 3, 3, 3, 3, 3, 3))
    ref_configs = set()
    for scc in sccs_ref:
        ref_configs.update(scc)

    # Check: what are the max values in each position?
    max_vals = [0] * n
    for c in ref_configs:
        for i in range(n):
            max_vals[i] = max(max_vals[i], c[i])
    print(f"  Max values in SCC configs: {max_vals}")
    print(f"  Reference ms:               {list((2, 2, 3, 3, 3, 3, 3, 3, 3))}")

    # Do all 492 configs have values < 2 for binary positions?
    bin_pos = [0, 1]  # for (2,2,3,3,...,3)
    max_at_bin = [0, 0]
    for c in ref_configs:
        for j, bp in enumerate(bin_pos):
            max_at_bin[j] = max(max_at_bin[j], c[bp])
    print(f"  Max values at binary positions {bin_pos}: {max_at_bin}")

    # Check: do any SCC configs use state 2 at ternary positions?
    tern_pos = list(range(2, 9))
    uses_state2 = [0] * n
    for c in ref_configs:
        for i in range(n):
            if c[i] == 2:
                uses_state2[i] += 1
    print(f"  Configs using state 2 at each pos: {uses_state2}")

    # KEY INSIGHT: if no SCC config uses state ≥ 2 at binary positions,
    # and no SCC config uses state ≥ 3 at ternary positions,
    # then the SCC configs are the same regardless of whether positions
    # are binary (m=2) or ternary (m=3) — because they only use states {0,1}!
    max_state_used = max(c[i] for c in ref_configs for i in range(n))
    print(f"\n  Maximum state value in ANY SCC config: {max_state_used}")
    if max_state_used <= 1:
        print("  *** ALL SCC CONFIGS USE ONLY STATES {0, 1}! ***")
        print("  This explains invariance: the 492 configs live in the {0,1}^9 subspace,")
        print("  which exists in ALL multisets with m_i ≥ 2.")
    elif max_state_used <= 2:
        print("  SCC configs use states {0, 1, 2} — need m_i ≥ 3 at positions using 2")

    # State distribution analysis
    print("\n  State value distribution across all 492 SCC configs:")
    for pos in range(n):
        vals = Counter(c[pos] for c in ref_configs)
        print(f"    pos {pos}: {dict(sorted(vals.items()))}")


def prod(ms):
    p = 1
    for m in ms:
        p *= m
    return p


if __name__ == "__main__":
    main()
