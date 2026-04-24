"""
Mixed-radix Gray code approach for self-stabilizing token rings.

Key insight: if ALL configurations are good (form a single Hamiltonian cycle),
then convergence is vacuously true (no bad configs), closure is trivial,
and liveness/mutual exclusion follow from the cycle structure.

The only remaining question: does a Hamiltonian cycle exist on the
mixed-radix configuration space where the induced transition functions
are CONSISTENT (same local view -> same privilege/output)?

This is why the all-binary Gray code works for n<=4 but fails for n=5:
with 5 binary processors, some local view must appear with conflicting
privilege requirements.
"""

import itertools
from typing import List, Tuple, Optional, Dict, Set
from collections import defaultdict
import time


def mixed_radix_gray_code(radices: List[int]) -> List[Tuple[int, ...]]:
    """
    Generate reflected mixed-radix Gray code.
    Returns list of all tuples, where consecutive tuples differ in one position.
    """
    if len(radices) == 0:
        return [()]

    if len(radices) == 1:
        return [(i,) for i in range(radices[0])]

    # Recursive: build Gray code for remaining positions
    sub_code = mixed_radix_gray_code(radices[1:])
    result = []

    for val in range(radices[0]):
        if val % 2 == 0:
            # Forward
            for sub in sub_code:
                result.append((val,) + sub)
        else:
            # Reversed
            for sub in reversed(sub_code):
                result.append((val,) + sub)

    return result


def check_consistency(cycle: List[Tuple[int, ...]], ms: List[int]) -> dict:
    """
    Check if a Hamiltonian cycle induces consistent transition functions.

    Returns dict with:
      'consistent': bool
      'conflicts': list of conflict descriptions
      'function_tables': dict of processor -> {(L,S,R) -> (privileged, output)}
    """
    n = len(ms)
    L = len(cycle)

    # Build the successor map and privilege assignment
    succ_map = {}
    mover_map = {}
    for idx in range(L):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % L]
        succ_map[c] = c_next
        # Find which position changed
        for j in range(n):
            if c[j] != c_next[j]:
                mover_map[c] = j
                break

    # Check fairness: all processors appear as movers
    movers = set(mover_map.values())
    if movers != set(range(n)):
        return {'consistent': False, 'reason': f'not all processors move: {movers}'}

    # Build function tables and check consistency
    function_tables = {}
    conflicts = []

    for i in range(n):
        table = {}  # (L, S, R) -> output value
        for c in cycle:
            l = c[(i - 1) % n]
            s = c[i]
            r = c[(i + 1) % n]
            key = (l, s, r)
            c_next = succ_map[c]

            if mover_map[c] == i:
                # Processor i is privileged: output = new state
                output = c_next[i]
                assert output != s
            else:
                # Processor i is NOT privileged: output = same state
                output = s

            if key in table:
                if table[key] != output:
                    conflicts.append(
                        f"P{i}: view ({l},{s},{r}) -> {table[key]} vs {output} "
                        f"(configs {c} and ...)"
                    )
            else:
                table[key] = output

        function_tables[i] = table

    return {
        'consistent': len(conflicts) == 0,
        'conflicts': conflicts,
        'function_tables': function_tables,
        'num_conflicts': len(conflicts),
    }


def analyze_conflicts(ms: List[int], verbose: bool = True) -> dict:
    """
    For a given state vector, generate the reflected Gray code and
    analyze its consistency for self-stabilization.
    """
    n = len(ms)
    total = 1
    for m in ms:
        total *= m

    if verbose:
        print(f"Analyzing ms={ms}, product={total}")

    cycle = mixed_radix_gray_code(ms)
    assert len(cycle) == total

    # Verify it's a valid Gray code (consecutive elements differ in one position)
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        diffs = sum(1 for j in range(n) if c[j] != c_next[j])
        if diffs != 1:
            print(f"  ERROR: step {idx} -> {idx+1} has {diffs} differences")
            return None

    result = check_consistency(cycle, ms)

    if verbose:
        if result['consistent']:
            print(f"  CONSISTENT! All configs good, valid system.")
        else:
            print(f"  {result['num_conflicts']} conflicts")
            for c in result['conflicts'][:5]:
                print(f"    {c}")
            if result['num_conflicts'] > 5:
                print(f"    ... and {result['num_conflicts'] - 5} more")

    return result


def search_gray_code_orderings(ms: List[int], max_attempts: int = 100000,
                                verbose: bool = True) -> Optional[dict]:
    """
    Search for a Hamiltonian cycle on the mixed-radix space
    that has consistent transition functions.

    Uses backtracking with conflict-driven pruning.
    """
    n = len(ms)
    total = 1
    for m in ms:
        total *= m

    if verbose:
        print(f"Searching for consistent Hamiltonian cycle on ms={ms}, total={total}")

    # For each processor i, track what local views are "claimed"
    # view_assignments[i][(L,S,R)] = output value (or None if unclaimed)
    all_configs = set(itertools.product(*(range(m) for m in ms)))

    best_length = [0]
    best_conflicts = [float('inf')]
    attempts = [0]
    start = time.time()

    def get_view(config, proc):
        return (config[(proc-1)%n], config[proc], config[(proc+1)%n])

    def backtrack(path, used, view_assign, mover_counts):
        """
        path: list of configs visited so far
        used: set of configs used
        view_assign: dict of {(proc, L, S, R) -> output} committed assignments
        mover_counts: dict of {proc -> count of times it's been the mover}
        """
        attempts[0] += 1
        if attempts[0] > max_attempts:
            return None

        if attempts[0] % 10000 == 0 and verbose:
            elapsed = time.time() - start
            print(f"  {attempts[0]} attempts, best_len={best_length[0]}/{total}, {elapsed:.1f}s")

        current = path[-1]
        path_len = len(path)

        if path_len > best_length[0]:
            best_length[0] = path_len

        if path_len == total:
            # Check: can we close the cycle back to path[0]?
            first = path[0]
            diffs = [(j, first[j]) for j in range(n) if current[j] != first[j]]
            if len(diffs) != 1:
                return None  # Can't close

            j, new_val = diffs[0]
            # Check consistency for this closing step
            view = get_view(current, j)
            key = (j,) + view
            if key in view_assign and view_assign[key] != new_val:
                return None  # Conflict

            # Also check: for all other processors, the view at current
            # must map to "not privileged" (output = current state)
            for proc in range(n):
                if proc == j:
                    continue
                view_p = get_view(current, proc)
                key_p = (proc,) + view_p
                if key_p in view_assign and view_assign[key_p] != current[proc]:
                    return None

            # Check fairness: all processors must have moved at least once
            final_mover_counts = dict(mover_counts)
            final_mover_counts[j] = final_mover_counts.get(j, 0) + 1
            if set(final_mover_counts.keys()) != set(range(n)):
                return None

            # Check consistency for path[0]: processor j was the mover
            # at the closing step, and all others should be non-privileged
            # at path[0] with the view from first config
            for proc in range(n):
                view_p = get_view(first, proc)
                key_p = (proc,) + view_p
                # At first, the mover is determined by path[0]->path[1]
                # This was already assigned when we built the path
                # So no new check needed here
                pass

            return list(path)

        # Generate candidates: configs that differ from current in one position
        # and are not yet used
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

                # Check consistency: processor j is privileged at current
                view_j = get_view(current, j)
                key_j = (j,) + view_j
                if key_j in view_assign:
                    if view_assign[key_j] == current[j]:
                        continue  # This view is non-privileged, can't use j as mover
                    if view_assign[key_j] != new_val:
                        continue  # Wrong output
                # Check: all other processors are NOT privileged at current
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

        # Sort candidates by some heuristic (prefer processors that haven't moved yet)
        candidates.sort(key=lambda x: (mover_counts.get(x[0], 0), x[0], x[1]))

        for j, new_val, next_config in candidates:
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
                    new_assigns[key_p] = current[proc]  # not privileged

            # Apply
            for k, v in new_assigns.items():
                view_assign[k] = v

            new_mover_counts = dict(mover_counts)
            new_mover_counts[j] = new_mover_counts.get(j, 0) + 1

            used.add(next_config)
            path.append(next_config)

            result = backtrack(path, used, view_assign, new_mover_counts)
            if result is not None:
                return result

            path.pop()
            used.remove(next_config)

            # Undo assignments
            for k in new_assigns:
                del view_assign[k]

        return None

    # Try starting from different initial configs
    start_configs = list(all_configs)[:10]  # Try first 10

    for start_config in start_configs:
        if verbose:
            print(f"  Starting from {start_config}...")
        result = backtrack(
            [start_config],
            {start_config},
            {},
            {}
        )
        if result is not None:
            if verbose:
                print(f"  Found Hamiltonian cycle of length {len(result)}!")
            # Verify
            check = check_consistency(result, ms)
            if check['consistent']:
                return {
                    'ms': ms,
                    'product': total,
                    'cycle': result,
                    'function_tables': check['function_tables'],
                }
            else:
                print(f"  WARNING: cycle found but inconsistent?!")
        if attempts[0] > max_attempts:
            break

    if verbose:
        elapsed = time.time() - start
        print(f"  No consistent cycle found ({attempts[0]} attempts, {elapsed:.1f}s)")
    return None


if __name__ == "__main__":
    print("=" * 60)
    print("MIXED-RADIX GRAY CODE ANALYSIS")
    print("=" * 60)
    print()

    # First, verify the known results
    print("--- Known results ---")
    for n in [3, 4]:
        analyze_conflicts([2] * n)
        print()

    # n=5 all binary (known to fail)
    print("--- n=5, all binary (expected to fail) ---")
    analyze_conflicts([2, 2, 2, 2, 2])
    print()

    # n=5, mixed radix candidates
    print("--- n=5, mixed radix candidates ---")
    candidates = [
        [2, 2, 2, 3, 3],  # product 72
        [2, 2, 3, 2, 3],  # product 72
        [2, 3, 2, 3, 2],  # product 72
        [2, 2, 3, 3, 3],  # product 108
        [2, 3, 2, 3, 3],  # product 108
        [2, 3, 3, 3, 3],  # product 162
        [3, 3, 3, 3, 2],  # product 162
    ]
    for ms in candidates:
        analyze_conflicts(ms)
        print()

    # For any that have few conflicts, try searching for better orderings
    print("\n--- Searching for consistent Hamiltonian cycles ---")
    # Start with smallest product
    for ms in [[2, 2, 2, 3, 3], [2, 2, 3, 2, 3], [2, 3, 2, 3, 2]]:
        result = search_gray_code_orderings(ms, max_attempts=50000)
        if result:
            print(f"\n*** FOUND: product={result['product']}, ms={result['ms']} ***")
            break
        print()
