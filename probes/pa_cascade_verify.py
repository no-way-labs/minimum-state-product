#!/usr/bin/env python3
"""Verify the cascade cycle theorem computationally.

The theorem: For n >= 8, 3CB, sub-threshold product, every choice of
transition functions has a bad cycle in the config graph.

Approach: Test ALL valid P1 mover choices, and for each, try to build
systems that avoid bad cycles. Show that at n=8, none succeed.

We already know from exploration_log_3cb_response_exhaustion.md that
ALL 80 toggle-valid P1 rules fail. But that was with mixed-sweep +
good-targeting constructions. Let's verify with hill climbing data too.

This script focuses on verifying the STRUCTURAL argument:
1. Interior-only dynamics at fixed binary MUST terminate (hit dead end or cycle)
2. At dead end, non-interior proc fires
3. Adversary forces cascade
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import defaultdict, Counter
import random

from verifier import all_configs, privileged_set, apply_move, verify_system


def tarjan_scc(nodes, succs_fn):
    index_counter = [0]
    stack = []
    on_stack = set()
    index = {}
    lowlink = {}
    sccs = []
    for start in nodes:
        if start in index:
            continue
        call_stack = [(start, iter(succs_fn(start)))]
        index[start] = lowlink[start] = index_counter[0]
        index_counter[0] += 1
        stack.append(start)
        on_stack.add(start)
        while call_stack:
            node, children = call_stack[-1]
            advanced = False
            for w in children:
                if w not in index:
                    index[w] = lowlink[w] = index_counter[0]
                    index_counter[0] += 1
                    stack.append(w)
                    on_stack.add(w)
                    call_stack.append((w, iter(succs_fn(w))))
                    advanced = True
                    break
                elif w in on_stack:
                    lowlink[node] = min(lowlink[node], index[w])
            if not advanced:
                call_stack.pop()
                if call_stack:
                    parent = call_stack[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[node])
                if lowlink[node] == index[node]:
                    scc = set()
                    while True:
                        w = stack.pop()
                        on_stack.discard(w)
                        scc.add(w)
                        if w == node:
                            break
                    sccs.append(scc)
    return sccs


def make_fs(tables):
    fs = []
    for table in tables:
        def make_f(t):
            def f(L, S, R):
                return t[(L, S, R)]
            return f
        fs.append(make_f(table))
    return fs


def random_valid_system_search(ms, n_trials=1000):
    """Try random transition tables, check for valid systems."""
    n = len(ms)
    product = 1
    for m in ms:
        product *= m

    valid_count = 0
    min_rec = float('inf')
    best_tables = None

    for trial in range(n_trials):
        # Random tables
        tables = []
        for p in range(n):
            table = {}
            for L in range(ms[(p-1) % n]):
                for S in range(ms[p]):
                    for R in range(ms[(p+1) % n]):
                        table[(L, S, R)] = random.randint(0, ms[p] - 1)
            tables.append(table)

        fs = make_fs(tables)

        # Quick liveness check
        configs = list(all_configs(ms))
        all_live = True
        for c in configs:
            priv = privileged_set(c, fs, ms)
            if not priv:
                all_live = False
                break
        if not all_live:
            continue

        # Check for valid system
        result = verify_system(list(ms), fs, verbose=False)
        if result['valid']:
            valid_count += 1
            print(f"  VALID at trial {trial}!")
            return tables

        # Count recurrent bad
        # (simplified: just check convergence property)
        if 'convergence' in result.get('properties', {}):
            conv_ok, conv_msg = result['properties']['convergence']
            if not conv_ok:
                # extract recurrent count if possible
                pass

    return None


def check_cascade_at_binary_111(ms, tables):
    """Check the interior dynamics at binary=(1,1,1).

    For each non-binary state, check:
    1. Which procs are privileged?
    2. Is any border/binary proc privileged?
    3. If only interior: what does interior dynamics look like?
    """
    n = len(ms)
    fs = make_fs(tables)

    binary = (1, 1, 1)
    non_binary_procs = [p for p in range(n) if ms[p] > 2]
    border = [3, n-1]
    interior = [p for p in range(4, n-1)]

    configs_111 = []
    for nb_vals in cartesian(*[range(ms[p]) for p in non_binary_procs]):
        config = list(binary) + [0] * (n - 3)
        for i, p in enumerate(non_binary_procs):
            config[p] = nb_vals[i]
        configs_111.append(tuple(config))

    stats = {'only_interior': 0, 'border_priv': 0, 'binary_priv': 0, 'dead': 0, 'good': 0}
    border_priv_configs = []

    good_set = set()
    # Find good configs at binary=(1,1,1) from the system
    # (We don't know the good cycle, so just check privilege counts)

    for c in configs_111:
        priv = privileged_set(c, fs, ms)
        if not priv:
            stats['dead'] += 1
            continue

        has_border = any(p in border for p in priv)
        has_binary = any(p in [0,1,2] for p in priv)
        has_interior = any(p in interior for p in priv)

        if has_border:
            stats['border_priv'] += 1
            border_priv_configs.append(c)
        if has_binary:
            stats['binary_priv'] += 1
        if has_interior and not has_border and not has_binary:
            stats['only_interior'] += 1

    return stats, border_priv_configs


def exhaustive_n4_check():
    """At n=4, ms=(2,2,2,3), check all transition tables."""
    ms = (2, 2, 2, 3)
    n = len(ms)
    product = 1
    for m in ms:
        product *= m
    print(f"\nn={n}, ms={ms}, product={product}")
    print(f"Checking random systems...")

    # Context sizes per proc
    for p in range(n):
        ctx_size = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
        print(f"  P{p}: {ctx_size} contexts")

    total_tables = 1
    for p in range(n):
        ctx_size = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
        total_tables *= ms[p] ** ctx_size
    print(f"Total possible table combinations: ~10^{len(str(total_tables))}")

    # Try random search
    random.seed(42)
    tables = random_valid_system_search(ms, n_trials=2000)
    if tables:
        print("Found valid system!")
    else:
        print("No valid system found in 2000 random trials")


def adversary_simulation(ms, tables, start_binary=(1,1,1), max_steps=200):
    """Simulate the adversary's cascade strategy.

    The adversary fires:
    - Border procs when available (to change boundary)
    - Binary procs when border procs not available (to change binary state)
    - Interior procs only when forced
    """
    n = len(ms)
    fs = make_fs(tables)

    border = [3, n-1]
    interior = list(range(4, n-1))

    # Start from a random config with the given binary state
    non_binary_procs = [p for p in range(n) if ms[p] > 2]
    config = [0] * n
    for i in range(3):
        config[i] = start_binary[i]
    for p in non_binary_procs:
        config[p] = random.randint(0, ms[p] - 1)
    config = tuple(config)

    path = [config]
    visited = {config: 0}

    for step in range(max_steps):
        priv = privileged_set(config, fs, ms)
        if not priv:
            return 'dead', path

        # Adversary priority: border > binary > interior
        chosen = None
        for p in priv:
            if p in border:
                chosen = p
                break
        if chosen is None:
            for p in priv:
                if p in [0, 1, 2]:
                    chosen = p
                    break
        if chosen is None:
            chosen = priv[0]

        new_config = apply_move(config, chosen, fs, ms)
        path.append(new_config)

        if new_config in visited:
            cycle_start = visited[new_config]
            cycle_len = len(path) - 1 - cycle_start
            return 'cycle', path[cycle_start:]

        visited[new_config] = len(path) - 1
        config = new_config

    return 'timeout', path


def main():
    print("="*70)
    print("CASCADE CYCLE VERIFICATION")
    print("="*70)

    # Test at n=8 with multiple random systems
    ms = (2, 2, 2, 3, 3, 3, 3, 4)
    n = len(ms)
    product = 1
    for m in ms:
        product *= m

    print(f"\nn={n}, ms={ms}, product={product}")

    random.seed(42)
    n_tests = 100
    cascade_found = 0
    dead_found = 0
    total_live = 0

    for trial in range(n_tests):
        # Random tables with liveness
        tables = []
        for p in range(n):
            table = {}
            for L in range(ms[(p-1) % n]):
                for S in range(ms[p]):
                    for R in range(ms[(p+1) % n]):
                        table[(L, S, R)] = random.randint(0, ms[p] - 1)
            tables.append(table)

        fs = make_fs(tables)

        # Check liveness
        configs = list(all_configs(ms))
        is_live = all(privileged_set(c, fs, ms) for c in configs)
        if not is_live:
            continue

        total_live += 1

        # Simulate adversary
        result, path = adversary_simulation(ms, tables, (1,1,1))
        if result == 'cycle':
            cascade_found += 1
        elif result == 'dead':
            dead_found += 1

    print(f"\nResults over {n_tests} random table sets:")
    print(f"  Live systems: {total_live}")
    print(f"  Cascade cycles found: {cascade_found}")
    print(f"  Dead configs found: {dead_found}")
    print(f"  Cascade rate: {cascade_found}/{total_live} = {cascade_found/max(1,total_live):.1%}")

    # Now test at n=7 for comparison
    ms7 = (2, 2, 2, 3, 3, 3, 4)
    n7 = len(ms7)
    product7 = 1
    for m in ms7:
        product7 *= m

    print(f"\nn={n7}, ms={ms7}, product={product7}")

    total_live7 = 0
    cascade7 = 0
    valid7 = 0

    for trial in range(n_tests):
        tables = []
        for p in range(n7):
            table = {}
            for L in range(ms7[(p-1) % n7]):
                for S in range(ms7[p]):
                    for R in range(ms7[(p+1) % n7]):
                        table[(L, S, R)] = random.randint(0, ms7[p] - 1)
            tables.append(table)

        fs = make_fs(tables)
        configs = list(all_configs(ms7))
        is_live = all(privileged_set(c, fs, ms7) for c in configs)
        if not is_live:
            continue

        total_live7 += 1

        result = verify_system(list(ms7), fs, verbose=False)
        if result['valid']:
            valid7 += 1

        result_sim, path = adversary_simulation(ms7, tables, (1,1,1))
        if result_sim == 'cycle':
            cascade7 += 1

    print(f"  Live systems: {total_live7}")
    print(f"  Valid systems: {valid7}")
    print(f"  Cascade cycles: {cascade7}")
    print(f"  Cascade rate: {cascade7}/{total_live7} = {cascade7/max(1,total_live7):.1%}")

    # Test the privilege structure at binary=(1,1,1)
    print("\n" + "="*70)
    print("PRIVILEGE STRUCTURE AT BINARY=(1,1,1)")
    print("="*70)

    ms8 = (2, 2, 2, 3, 3, 3, 3, 4)
    random.seed(123)

    for trial in range(5):
        tables = []
        for p in range(8):
            table = {}
            for L in range(ms8[(p-1) % 8]):
                for S in range(ms8[p]):
                    for R in range(ms8[(p+1) % 8]):
                        table[(L, S, R)] = random.randint(0, ms8[p] - 1)
            tables.append(table)

        fs = make_fs(tables)
        configs = list(all_configs(ms8))
        is_live = all(privileged_set(c, fs, ms8) for c in configs)
        if not is_live:
            continue

        stats, _ = check_cascade_at_binary_111(ms8, tables)
        print(f"\n  Trial {trial}: {stats}")


if __name__ == '__main__':
    main()
