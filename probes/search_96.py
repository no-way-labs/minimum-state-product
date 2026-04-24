"""
Search for valid self-stabilizing systems at product 96 for n=5.
Target state vectors: (2,2,2,3,4) and (2,2,3,2,4).

Strategy: good-cycle-first approach.
1. Enumerate locally consistent good cycles
2. Check what rule entries each cycle forces
3. Test whether the forced rules + extension to bad configs yield convergence
"""

import itertools
import time
from typing import List, Tuple, Optional, Dict, Set
from collections import defaultdict
from verifier import verify_system


def enumerate_good_cycles(ms: List[int], max_cycles: int = 10000,
                          verbose: bool = True) -> list:
    """
    Enumerate locally consistent good cycles for a given state vector.

    A good cycle is a sequence c_0, c_1, ..., c_{L-1} such that:
    - Consecutive configs differ in exactly one position (the mover)
    - At each config, only the mover's local view is "privileged"
    - All assignments are consistent (same local view -> same output)
    - All n processors move at least once (fairness)
    """
    n = len(ms)
    total = 1
    for m in ms:
        total *= m

    all_configs = list(itertools.product(*(range(m) for m in ms)))
    config_set = set(all_configs)

    found_cycles = []
    attempts = [0]
    start = time.time()

    def get_view(config, proc):
        return (config[(proc-1)%n], config[proc], config[(proc+1)%n])

    def backtrack(path, used, view_assign, mover_set):
        """
        path: list of configs in cycle so far
        used: set of configs used
        view_assign: {(proc, L, S, R) -> output} for assigned views
        mover_set: set of processors that have moved
        """
        attempts[0] += 1
        if attempts[0] > 500000:
            return

        current = path[-1]
        path_len = len(path)

        # Try to close the cycle if long enough (>= n) and all processors moved
        if path_len >= n and len(mover_set) == n:
            first = path[0]
            diffs = [(j, first[j]) for j in range(n) if current[j] != first[j]]
            if len(diffs) == 1:
                j, new_val = diffs[0]
                # Check consistency for closing step
                view_j = get_view(current, j)
                key_j = (j,) + view_j
                if key_j in view_assign and view_assign[key_j] != new_val:
                    pass  # Conflict
                elif view_j[1] == new_val:
                    pass  # Not a real move
                else:
                    # Check non-movers at current config
                    ok = True
                    for proc in range(n):
                        if proc == j:
                            continue
                        view_p = get_view(current, proc)
                        key_p = (proc,) + view_p
                        if key_p in view_assign and view_assign[key_p] != current[proc]:
                            ok = False
                            break
                    if ok:
                        # Valid cycle!
                        cycle = list(path)
                        found_cycles.append(cycle)
                        if verbose and len(found_cycles) <= 5:
                            print(f"  Found cycle #{len(found_cycles)}, length={path_len}")
                        if len(found_cycles) >= max_cycles:
                            return

        # Don't search too deep
        if path_len >= total:
            return

        # Generate candidates
        candidates = []
        for j in range(n):
            for new_val in range(ms[j]):
                if new_val == current[j]:
                    continue
                next_config = list(current)
                next_config[j] = new_val
                next_config = tuple(next_config)
                if next_config in used:
                    continue

                # Check consistency
                view_j = get_view(current, j)
                key_j = (j,) + view_j

                if key_j in view_assign:
                    if view_assign[key_j] == current[j]:
                        continue  # View is non-privileged
                    if view_assign[key_j] != new_val:
                        continue  # Wrong output
                elif view_j[1] == new_val:
                    continue  # Would mean f(L,S,R) = S, not privileged

                # Check non-movers
                conflict = False
                for proc in range(n):
                    if proc == j:
                        continue
                    view_p = get_view(current, proc)
                    key_p = (proc,) + view_p
                    if key_p in view_assign and view_assign[key_p] != current[proc]:
                        conflict = True
                        break
                if conflict:
                    continue

                candidates.append((j, new_val, next_config))

        # Prioritize: processors that haven't moved yet
        candidates.sort(key=lambda x: (x[0] in mover_set, x[0], x[1]))

        for j, new_val, next_config in candidates:
            if len(found_cycles) >= max_cycles:
                return

            # Commit assignments
            new_assigns = {}
            view_j = get_view(current, j)
            key_j = (j,) + view_j
            if key_j not in view_assign:
                new_assigns[key_j] = new_val

            for proc in range(n):
                if proc == j:
                    continue
                view_p = get_view(current, proc)
                key_p = (proc,) + view_p
                if key_p not in view_assign:
                    new_assigns[key_p] = current[proc]

            for k, v in new_assigns.items():
                view_assign[k] = v

            new_mover = mover_set | {j}
            used.add(next_config)
            path.append(next_config)

            backtrack(path, used, view_assign, new_mover)

            path.pop()
            used.remove(next_config)
            for k in new_assigns:
                del view_assign[k]

    # Try starting from a few configs
    start_configs = all_configs[:20]
    for sc in start_configs:
        if len(found_cycles) >= max_cycles:
            break
        if verbose:
            print(f"  Starting from {sc}...")
        backtrack([sc], {sc}, {}, set())

    elapsed = time.time() - start
    if verbose:
        print(f"  {len(found_cycles)} cycles found, {attempts[0]} nodes explored, {elapsed:.1f}s")

    return found_cycles


def complete_and_verify(ms: List[int], cycle: list, verbose: bool = False) -> Optional[dict]:
    """
    Given a good cycle, complete the transition functions for all configs
    and verify the full system.

    Strategy:
    1. Extract forced rule entries from the cycle
    2. For unforced entries, try to assign values that ensure convergence
    """
    n = len(ms)
    total = 1
    for m in ms:
        total *= m

    # Build successor map and forced assignments
    view_assign = {}  # (proc, L, S, R) -> output
    cycle_set = set(map(tuple, cycle))

    for idx in range(len(cycle)):
        c = tuple(cycle[idx])
        c_next = tuple(cycle[(idx + 1) % len(cycle)])

        # Find mover
        mover = None
        for j in range(n):
            if c[j] != c_next[j]:
                mover = j
                break

        for proc in range(n):
            view = (c[(proc-1)%n], c[proc], c[(proc+1)%n])
            key = (proc,) + view
            if proc == mover:
                view_assign[key] = c_next[proc]
            else:
                view_assign[key] = c[proc]  # not privileged

    # Build transition functions
    # For entries not determined by the cycle, we need to choose.
    # Key constraint: liveness (every config must have a privileged processor)
    # and convergence (no bad cycles).

    # Try: for unforced entries, default to "not privileged" (f = S)
    # unless this violates liveness
    all_configs = list(itertools.product(*(range(m) for m in ms)))

    def make_f_default(proc):
        """Default: use forced assignments, else f(L,S,R) = S."""
        def f(L, S, R):
            key = (proc, L, S, R)
            if key in view_assign:
                return view_assign[key]
            return S
        return f

    fs_default = [make_f_default(i) for i in range(n)]

    # Check liveness with default
    dead_configs = []
    for c in all_configs:
        has_priv = False
        for i in range(n):
            view = (c[(i-1)%n], c[i], c[(i+1)%n])
            if fs_default[i](*view) != c[i]:
                has_priv = True
                break
        if not has_priv:
            dead_configs.append(c)

    if dead_configs:
        # Need to fix liveness for dead configs
        # For each dead config, find an unforced view and make it privileged
        view_fixes = {}
        for c in dead_configs:
            fixed = False
            for i in range(n):
                view = (c[(i-1)%n], c[i], c[(i+1)%n])
                key = (i,) + view
                if key not in view_assign:
                    # Make this view privileged: output != S
                    # Choose output = (S + 1) % m_i
                    new_val = (c[i] + 1) % ms[i]
                    # But check we don't conflict with other assignments
                    if key not in view_fixes or view_fixes[key] == new_val:
                        view_fixes[key] = new_val
                        fixed = True
                        break
            if not fixed:
                return None  # Can't fix liveness

        # Merge fixes
        for key, val in view_fixes.items():
            view_assign[key] = val

    # Rebuild functions with fixes
    def make_f(proc):
        def f(L, S, R):
            key = (proc, L, S, R)
            if key in view_assign:
                return view_assign[key]
            return S
        return f

    fs = [make_f(i) for i in range(n)]

    # Verify
    result = verify_system(ms, fs)
    return result if result['valid'] else None


def search_product_96(verbose: bool = True):
    """Search for valid systems at product 96 for n=5."""
    targets = [
        [2, 2, 2, 3, 4],
        [2, 2, 3, 2, 4],
        [2, 2, 2, 4, 3],
        [2, 2, 4, 2, 3],
        [2, 2, 4, 3, 2],
        [2, 4, 2, 2, 3],
        [2, 4, 2, 3, 2],
        [2, 4, 3, 2, 2],
        [4, 2, 2, 2, 3],
        [4, 2, 2, 3, 2],
        [4, 2, 3, 2, 2],
        [2, 3, 2, 2, 4],
        [2, 3, 2, 4, 2],
        [2, 3, 4, 2, 2],
        [3, 2, 2, 2, 4],
        [3, 2, 2, 4, 2],
        [3, 2, 4, 2, 2],
        [3, 4, 2, 2, 2],
        [4, 3, 2, 2, 2],
        [4, 2, 2, 2, 3],  # dup but different rotation context
    ]

    # Filter: no 4+ consecutive binary
    from smt_search import has_four_consecutive_binary, canonical_rotation
    seen = set()
    feasible = []
    for t in targets:
        if has_four_consecutive_binary(t):
            continue
        canon = canonical_rotation(tuple(t))
        if canon in seen:
            continue
        seen.add(canon)
        feasible.append(t)

    if verbose:
        print(f"Feasible product-96 vectors: {len(feasible)}")
        for v in feasible:
            print(f"  {v}")
        print()

    for ms in feasible:
        if verbose:
            print(f"=== Searching ms={ms} ===")

        cycles = enumerate_good_cycles(ms, max_cycles=100, verbose=verbose)

        if not cycles:
            if verbose:
                print(f"  No good cycles found")
            continue

        if verbose:
            print(f"  Testing {len(cycles)} cycles for completability...")

        for i, cycle in enumerate(cycles):
            result = complete_and_verify(ms, cycle, verbose=False)
            if result:
                if verbose:
                    print(f"  VALID! Cycle #{i+1}, length={len(cycle)}, "
                          f"verified cycle_len={result['cycle_length']}")
                return {
                    'ms': ms,
                    'product': 96,
                    'cycle': cycle,
                    'verification': result,
                }

        if verbose:
            print(f"  No completable cycles found with default strategy")
            print()

    return None


if __name__ == "__main__":
    print("=" * 60)
    print("SEARCH FOR M_5 = 96 CONSTRUCTIONS")
    print("State vectors: permutations of {2,2,2,3,4}")
    print("=" * 60)
    print()

    result = search_product_96(verbose=True)

    if result:
        print(f"\n*** VERIFIED: product 96 system with ms={result['ms']} ***")
        print(f"Cycle length: {result['verification']['cycle_length']}")
    else:
        print("\nDefault completion strategy failed.")
        print("Need smarter rule completion for off-cycle configs.")
