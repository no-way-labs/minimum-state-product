#!/usr/bin/env python3
"""scc_bounce_test.py — Test bounce-pattern cycles at lower products.

Dijkstra Sol 3 uses a "bounce" mover pattern:
  [8,7,6,...,1,0,1,2,...,7,8,7,...,1,0,1,...,8]

This pattern creates ZERO bad SCCs at product 19683 = 3^9.
Question: can we construct similar bounce-pattern cycles at lower products?
Do they also avoid the 3 bad SCCs?
"""

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


def construct_bounce_cycle(ms, n, nb_val=1):
    """Construct a bounce-pattern cycle for given state counts.

    Pattern: sweep down n-1,...,0 then sweep up 1,...,n-1, repeating.
    At each step, the moving processor changes state.

    For Sol 3 at (3,3,...,3):
      Down sweep: proc changes from some value to another
      Up sweep: proc changes from some value to another

    We'll try: start at all-zeros, sweep down changing 0→nb, sweep up changing nb→0, etc.
    But this needs to respect the available states.
    """
    config = [0] * n
    cycle = [tuple(config)]

    # Sweep down: n-1, n-2, ..., 1, 0
    for proc in range(n - 1, -1, -1):
        config = list(cycle[-1])
        new_val = nb_val if ms[proc] > nb_val else 1
        if config[proc] == new_val:
            return None  # Can't change
        config[proc] = new_val
        cycle.append(tuple(config))

    # Sweep up: 1, 2, ..., n-1
    for proc in range(1, n):
        config = list(cycle[-1])
        config[proc] = 0
        if tuple(config) in set(cycle):
            return None  # Collision
        cycle.append(tuple(config))

    # Now continue the pattern to close the cycle
    # We need to get back to (0,0,...,0)
    # After down sweep: all = nb_val
    # After up sweep 1..n-1: (nb_val, 0, 0, ..., 0)
    # Need proc 0 to go back to 0
    config = list(cycle[-1])
    if config[0] != 0:
        config[0] = 0
        if tuple(config) == cycle[0]:
            # Cycle closed
            pass
        else:
            cycle.append(tuple(config))

    # Remove duplicate if last == first
    if cycle[-1] == cycle[0]:
        cycle = cycle[:-1]

    return cycle


def construct_sol3_bounce(ms, n, K=3):
    """Construct the Sol 3-style bounce cycle.

    For all-ternary (3,...,3), the bounce pattern is:
    Start at some legitimate config, follow single-privilege transitions.
    The mover pattern is: n-1, n-2, ..., 0, 1, 2, ..., n-1, n-2, ..., 0, ...

    For mixed state counts, we need to adapt. The key idea:
    - Use 3 phases (for K=3 states): 0→1→2→0 cycle in state values
    - Each phase does a bounce (sweep down + sweep up)
    """
    # Try to build a cycle manually
    # Phase 1: all-0 → sweep down to all-1 → sweep up P1..P_{n-1} back to 0
    # (leaves P0 at 1)
    # Phase 2: (1,0,...,0) → sweep down to all-?
    # This is complex. Let me try a different approach.

    # Just try various bounce patterns and check for good cycles
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}

    # Try: sweep down changing 0→1, sweep up changing 1→0 (for positions > 0)
    # This gives a length-(2n-1) cycle for the up-down bounce

    # Pattern 1: Simple bounce [n-1, n-2, ..., 0, 1, 2, ..., n-1]
    # = length 2n-1 bounce
    movers_pattern = list(range(n-1, -1, -1)) + list(range(1, n))
    # Repeat this pattern multiple times if needed

    for repeat in range(1, 4):
        config = [0] * n
        cycle = [tuple(config)]
        visited = {tuple(config)}

        full_movers = movers_pattern * repeat
        valid = True

        for step, mover in enumerate(full_movers):
            config = list(cycle[-1])
            # Change state: cycle through available values
            current = config[mover]
            new_val = (current + 1) % ms[mover]
            config[mover] = new_val
            new_config = tuple(config)

            if new_config in visited and new_config != cycle[0]:
                valid = False
                break

            if new_config == cycle[0]:
                # Cycle closed!
                cycle_movers = full_movers[:step + 1]
                return cycle, cycle_movers

            visited.add(new_config)
            cycle.append(new_config)

    return None, None


def check_scc_for_cycle(ms, cycle, movers, n):
    """Check bad SCCs for a given good cycle."""
    # Build determined entries
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

    good_set = set(cycle)
    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    forced_succs = {}
    for c in non_good:
        succs = []
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
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
    sizes = sorted([len(s) for s in sccs], reverse=True)
    return len(sccs), sum(sizes), sizes


def main():
    n = 9
    print("=" * 70)
    print("BOUNCE-PATTERN CYCLE TEST AT LOWER PRODUCTS")
    print("=" * 70)

    # Test 1: All-ternary, bounce cycles
    print("\n--- Test 1: All-ternary (3^9 = 19683) ---")
    ms_all3 = (3,) * n

    cycle, movers = construct_sol3_bounce(ms_all3, n)
    if cycle:
        print(f"  Bounce cycle found: length {len(cycle)}")
        print(f"  Movers: {movers[:40]}...")
        n_sccs, n_configs, sizes = check_scc_for_cycle(ms_all3, cycle, movers, n)
        print(f"  SCCs: {n_sccs}, total configs: {n_configs}")
        if sizes:
            print(f"  SCC sizes: {sizes[:10]}")
    else:
        print("  No bounce cycle found via simple construction")

    # Test 2: Try bounce at product 13122 = 2·3^8
    print("\n--- Test 2: Product 13122 (2, 3^8) ---")
    ms_13122 = (2, 3, 3, 3, 3, 3, 3, 3, 3)

    cycle, movers = construct_sol3_bounce(ms_13122, n)
    if cycle:
        print(f"  Bounce cycle found: length {len(cycle)}")
        print(f"  Movers: {movers[:40]}...")
        n_sccs, n_configs, sizes = check_scc_for_cycle(ms_13122, cycle, movers, n)
        print(f"  SCCs: {n_sccs}, total configs: {n_configs}")
        if sizes:
            print(f"  SCC sizes: {sizes[:10]}")
    else:
        print("  No bounce cycle found")

    # Test 3: Try bounce at product 8748 = 2^2·3^7
    print("\n--- Test 3: Product 8748 (2, 2, 3^7) ---")
    ms_8748 = (2, 2, 3, 3, 3, 3, 3, 3, 3)

    cycle, movers = construct_sol3_bounce(ms_8748, n)
    if cycle:
        print(f"  Bounce cycle found: length {len(cycle)}")
        print(f"  Movers: {movers[:40]}...")
        n_sccs, n_configs, sizes = check_scc_for_cycle(ms_8748, cycle, movers, n)
        print(f"  SCCs: {n_sccs}, total configs: {n_configs}")
    else:
        print("  No bounce cycle found")

    # Test 4: Enumerate many bounce-type cycles for all-ternary
    print("\n--- Test 4: Systematic bounce cycles for (3^9) ---")
    ms = (3,) * n

    # Try various bounce patterns
    patterns = [
        ("down-up", list(range(n-1, -1, -1)) + list(range(1, n))),
        ("up-down", list(range(n)) + list(range(n-2, 0, -1))),
        ("down-up-down", list(range(n-1, -1, -1)) + list(range(1, n)) + list(range(n-2, 0, -1))),
    ]

    for name, base_pattern in patterns:
        for repeats in range(1, 5):
            config = [0] * n
            cycle = [tuple(config)]
            visited = {tuple(config)}
            full_movers = base_pattern * repeats

            valid = True
            actual_movers = []
            for step, mover in enumerate(full_movers):
                config = list(cycle[-1])
                current = config[mover]
                new_val = (current + 1) % ms[mover]
                config[mover] = new_val
                new_config = tuple(config)

                if new_config in visited and new_config != cycle[0]:
                    valid = False
                    break

                if new_config == cycle[0]:
                    actual_movers = full_movers[:step + 1]
                    valid = True
                    break

                visited.add(new_config)
                cycle.append(new_config)
                actual_movers = full_movers[:step + 1]
            else:
                # Didn't close
                valid = False

            if valid and actual_movers:
                n_sccs, n_configs, sizes = check_scc_for_cycle(ms, cycle, actual_movers, n)
                status = "CLEAN" if n_sccs == 0 else f"{n_sccs} SCCs ({n_configs})"
                print(f"  {name}×{repeats}: len={len(cycle)}, {status}")
                if sizes:
                    print(f"    SCC sizes: {sizes[:5]}")

    # Test 5: Can we construct a bounce cycle for lower products?
    # The key challenge: with m_i = 2, processor i can only go 0→1→0
    # In a bounce cycle, each processor needs to change value multiple times
    # Binary processors limit this severely
    print("\n--- Test 5: Bounce cycle feasibility with binary processors ---")
    for ms_test in [
        (2, 3, 3, 3, 3, 3, 3, 3, 3),   # 1 binary
        (2, 2, 3, 3, 3, 3, 3, 3, 3),   # 2 binary
        (3, 3, 3, 3, 3, 3, 3, 3, 3),   # all ternary (reference)
    ]:
        # Try up-down bounce × various repeats
        for base in [list(range(n)) + list(range(n-2, 0, -1)),
                     list(range(n-1, -1, -1)) + list(range(1, n))]:
            for repeats in range(1, 5):
                config = [0] * n
                cycle = [tuple(config)]
                visited = {tuple(config)}
                full_movers = base * repeats

                actual_movers = []
                closed = False
                for step, mover in enumerate(full_movers):
                    config = list(cycle[-1])
                    current = config[mover]
                    new_val = (current + 1) % ms_test[mover]
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
                    n_sccs, n_configs, sizes = check_scc_for_cycle(
                        ms_test, cycle, actual_movers, n)
                    status = "CLEAN" if n_sccs == 0 else f"{n_sccs} SCCs ({n_configs})"
                    bin_count = sum(1 for m in ms_test if m == 2)
                    print(f"  ms={ms_test} ({bin_count} bin), reps={repeats}: "
                          f"len={len(cycle)}, {status}")
                    if n_sccs == 0:
                        print(f"    *** CLEAN BOUNCE CYCLE FOUND! ***")
                    break  # Found a cycle for this repeat count


if __name__ == "__main__":
    main()
