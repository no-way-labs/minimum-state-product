#!/usr/bin/env python3
"""scc_completion_test.py — Try to complete bounce cycles into full systems.

A clean bounce cycle (no bad SCCs) is necessary but not sufficient.
We need to fill in ALL free entries in the rule table to create a
valid self-stabilizing system. Try:
1. Build the determined entries from the bounce cycle
2. Check what fraction of entries are determined
3. Try to complete the remaining entries
4. Verify the complete system
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import Counter


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


def construct_bounce_cycle(ms, n):
    """Construct a bounce cycle: down sweep then up sweep, repeating."""
    base_pattern = list(range(n-1, -1, -1)) + list(range(1, n))

    for repeats in range(1, 5):
        config = [0] * n
        cycle = [tuple(config)]
        visited = {tuple(config)}
        full_movers = base_pattern * repeats

        actual_movers = []
        closed = False
        for step, mover in enumerate(full_movers):
            config = list(cycle[-1])
            current = config[mover]
            new_val = (current + 1) % ms[mover]
            config[mover] = new_val
            new_config = tuple(config)

            if new_config in visited and new_config != cycle[0]:
                break

            if new_config == cycle[0]:
                actual_movers = full_movers[:step + 1]
                closed = True
                break

            visited.add(new_config)
            cycle.append(new_config)

        if closed:
            return cycle, actual_movers

    return None, None


def get_determined_entries(cycle, movers, n):
    """Extract determined entries from a good cycle."""
    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        mover = movers[idx]
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            if i == mover:
                det[(i, L, S, R)] = c_next[i]
            else:
                det[(i, L, S, R)] = S
    return det


def try_greedy_completion(ms, cycle, movers, n):
    """Greedily complete the rule table.

    Strategy: for each free entry (i, L, S, R), set f(i, L, S, R) = S
    (no change = not privileged). This minimizes privileges at non-good configs,
    which should help convergence.

    Then check the complete system.
    """
    det = get_determined_entries(cycle, movers, n)

    # Fill free entries with "no change" (S)
    complete = dict(det)
    for i in range(n):
        for L in range(ms[(i-1) % n]):
            for S in range(ms[i]):
                for R in range(ms[(i+1) % n]):
                    key = (i, L, S, R)
                    if key not in complete:
                        complete[key] = S  # No change = not privileged

    return complete


def try_convergent_completion(ms, cycle, movers, n):
    """Complete the rule table aiming for convergence.

    Strategy: for free entries, try to make the config converge toward
    the good cycle. For (i, L, S, R) free, check if setting f = S leaves
    configs without privilege (deadlock risk) or creates SCCs.
    """
    det = get_determined_entries(cycle, movers, n)
    good_set = set(cycle)

    # Start with greedy (all free = S)
    complete = dict(det)
    free_keys = []
    for i in range(n):
        for L in range(ms[(i-1) % n]):
            for S in range(ms[i]):
                for R in range(ms[(i+1) % n]):
                    key = (i, L, S, R)
                    if key not in complete:
                        complete[key] = S
                        free_keys.append(key)

    # Check for deadlocks
    all_configs = list(cartesian(*(range(m) for m in ms)))
    deadlocks = []
    for c in all_configs:
        if c in good_set:
            continue
        has_priv = False
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            if complete[(i, L, S, R)] != S:
                has_priv = True
                break
        if not has_priv:
            deadlocks.append(c)

    return complete, deadlocks


def verify_complete_system(ms, complete, cycle, n, det=None):
    """Check all 5 properties of the complete system."""
    good_set = set(cycle)
    all_configs = list(cartesian(*(range(m) for m in ms)))

    # 1. Liveness: every config has at least 1 privilege
    deadlocks = []
    for c in all_configs:
        has_priv = False
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            if complete[(i, L, S, R)] != S:
                has_priv = True
                break
        if not has_priv:
            deadlocks.append(c)

    # 2. Mutual exclusion: good configs have exactly 1 privilege
    bad_good = []
    for c in good_set:
        n_priv = sum(1 for i in range(n)
                     if complete[(i, c[(i-1)%n], c[i], c[(i+1)%n])] != c[i])
        if n_priv != 1:
            bad_good.append((c, n_priv))

    # 3. Closure: good cycle transitions stay in good set
    closure_ok = True
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        # Find mover
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            closure_ok = False
            break
        mover = diffs[0]
        L = c[(mover-1) % n]; S = c[mover]; R = c[(mover+1) % n]
        if complete[(mover, L, S, R)] != c_next[mover]:
            closure_ok = False
            break

    # 4. Convergence: no cycles among non-good configs
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    forced_succs = {}
    for c in non_good:
        succs = []
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            new_val = complete[(i, L, S, R)]
            if new_val != S:
                new_c = list(c)
                new_c[i] = new_val
                new_c = tuple(new_c)
                if new_c in non_good_set:
                    succs.append(new_c)
        if succs:
            forced_succs[c] = succs

    sccs = find_sccs(forced_succs)
    scc_sizes = sorted([len(s) for s in sccs], reverse=True)

    return {
        'deadlocks': len(deadlocks),
        'bad_good': len(bad_good),
        'closure': closure_ok,
        'n_sccs': len(sccs),
        'scc_total': sum(scc_sizes),
        'scc_sizes': scc_sizes[:10],
        'n_free': len(complete) - (len(det) if det else 0)
    }


def main():
    n = 9
    print("=" * 70)
    print("BOUNCE CYCLE COMPLETION TEST")
    print("=" * 70)

    test_cases = [
        (3,) * 9,                                      # 19683
        (2, 3, 3, 3, 3, 3, 3, 3, 3),                  # 13122
        (2, 2, 3, 3, 3, 3, 3, 3, 3),                  # 8748
        (2, 2, 2, 3, 3, 3, 3, 3, 3),                  # 5832
        (2, 2, 2, 2, 3, 3, 3, 3, 3),                  # 3888
        (2, 2, 2, 2, 2, 3, 3, 3, 3),                  # 2592 = M_8
    ]

    for ms in test_cases:
        ms_list = list(ms)
        product = 1
        for m in ms:
            product *= m
        bin_count = sum(1 for m in ms if m == 2)

        print(f"\n{'─' * 60}")
        print(f"ms={ms}, product={product}, {bin_count} binary")
        print(f"{'─' * 60}")

        cycle, movers = construct_bounce_cycle(ms_list, n)
        if not cycle:
            print("  No bounce cycle found")
            continue

        print(f"  Bounce cycle: length {len(cycle)}")
        print(f"  Movers: {movers[:30]}...")

        det = get_determined_entries(cycle, movers, n)
        total_entries = sum(ms[(i-1)%n] * ms[i] * ms[(i+1)%n] for i in range(n))
        n_forcing = sum(1 for k, v in det.items() if v != k[2])
        print(f"  Determined: {len(det)}/{total_entries} ({100*len(det)/total_entries:.1f}%)")
        print(f"  Forcing: {n_forcing}")

        # Try greedy completion
        complete = try_greedy_completion(ms_list, cycle, movers, n)

        # Verify
        result = verify_complete_system(ms_list, complete, cycle, n, det=det)
        print(f"  Greedy completion:")
        print(f"    Deadlocks: {result['deadlocks']}")
        print(f"    Bad good configs: {result['bad_good']}")
        print(f"    Closure: {result['closure']}")
        print(f"    SCCs: {result['n_sccs']}, total {result['scc_total']}")
        if result['scc_sizes']:
            print(f"    SCC sizes: {result['scc_sizes']}")

        if result['deadlocks'] == 0 and result['bad_good'] == 0 and result['closure'] and result['n_sccs'] == 0:
            print(f"    *** VALID SYSTEM AT PRODUCT {product}! ***")

        # If there are deadlocks, try to fix them
        if result['deadlocks'] > 0:
            print(f"\n  Fixing deadlocks...")
            complete2, deadlocks2 = try_convergent_completion(ms_list, cycle, movers, n)

            # For each deadlock, try to make some processor privileged
            # by changing a free entry
            fixed = 0
            remaining_deadlocks = []
            for c in deadlocks2:
                found_fix = False
                for i in range(n):
                    L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
                    key = (i, L, S, R)
                    if key not in det:  # Free entry
                        # Try setting it to any value ≠ S
                        for v in range(ms[i]):
                            if v != S:
                                # Check: would this create a conflict with any good config?
                                # The entry is free, so it shouldn't conflict
                                complete2[key] = v
                                found_fix = True
                                fixed += 1
                                break
                    if found_fix:
                        break
                if not found_fix:
                    remaining_deadlocks.append(c)

            # Re-verify
            result2 = verify_complete_system(ms_list, complete2, cycle, n)
            print(f"  After fixing {fixed} deadlocks:")
            print(f"    Remaining deadlocks: {result2['deadlocks']}")
            print(f"    SCCs: {result2['n_sccs']}, total {result2['scc_total']}")
            if result2['scc_sizes']:
                print(f"    SCC sizes: {result2['scc_sizes']}")

            if result2['deadlocks'] == 0 and result2['bad_good'] == 0 and result2['closure'] and result2['n_sccs'] == 0:
                print(f"    *** VALID SYSTEM AT PRODUCT {product}! ***")

                # Double-check with verifier
                print(f"\n  Verifying with verifier.py...")
                try:
                    from verifier import verify_system
                    # Build rule functions
                    rule_fns = []
                    for i in range(n):
                        def make_fn(proc_i, comp, ms_local):
                            def fn(L, S, R):
                                return comp[(proc_i, L, S, R)]
                            return fn
                        rule_fns.append(make_fn(i, complete2, ms_list))
                    vresult = verify_system(ms_list, rule_fns)
                    print(f"    verify_system: {vresult.get('valid', 'error')}")
                    if vresult.get('valid'):
                        props = vresult.get('properties', {})
                        for k, v in props.items():
                            print(f"      {k}: {v}")
                except Exception as e:
                    print(f"    Verifier error: {e}")


if __name__ == "__main__":
    main()
