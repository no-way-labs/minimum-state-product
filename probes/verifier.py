"""
Self-Stabilizing Token Ring Verifier and Searcher

Verifies the 5 Dijkstra properties for a token ring system:
1. Liveness: every configuration has at least one privileged processor
2. Mutual exclusion: every good configuration has exactly one privileged processor
3. Closure: moves from good configs lead to good configs
4. Convergence: no cycle of bad configurations exists
5. Fairness: the good-config cycle visits every processor

Given n processors with state counts (m_0, ..., m_{n-1}), each processor
P_i has a transition function f_i(L, S, R) -> S' where L, S, R are the
states of the left neighbor, self, and right neighbor.

P_i is privileged iff f_i(L, S, R) != S.
"""

import itertools
from typing import List, Tuple, Optional, Set, Dict
from collections import defaultdict


def all_configs(ms: List[int]):
    """Generate all configurations for state vector ms."""
    return itertools.product(*(range(m) for m in ms))


def privileged_set(config: Tuple[int, ...], fs: List, ms: List[int]) -> List[int]:
    """Return list of privileged processor indices in this configuration."""
    n = len(ms)
    priv = []
    for i in range(n):
        L = config[(i - 1) % n]
        S = config[i]
        R = config[(i + 1) % n]
        if fs[i](L, S, R) != S:
            priv.append(i)
    return priv


def apply_move(config: Tuple[int, ...], i: int, fs: List, ms: List[int]) -> Tuple[int, ...]:
    """Apply processor i's transition, return new configuration."""
    n = len(ms)
    L = config[(i - 1) % n]
    S = config[i]
    R = config[(i + 1) % n]
    new_s = fs[i](L, S, R)
    lst = list(config)
    lst[i] = new_s
    return tuple(lst)


def verify_system(ms: List[int], fs: List, verbose: bool = False) -> dict:
    """
    Verify all 5 properties of a self-stabilizing token ring.

    Returns dict with:
      'valid': bool
      'properties': dict of property_name -> (bool, info)
      'good_configs': set of good configurations (if valid)
    """
    n = len(ms)
    total = 1
    for m in ms:
        total *= m

    # Compute privilege sets for all configurations
    configs = list(all_configs(ms))
    priv_map = {}  # config -> list of privileged processors
    for c in configs:
        priv_map[c] = privileged_set(c, fs, ms)

    # Property 1: Liveness
    dead_configs = [c for c in configs if len(priv_map[c]) == 0]
    liveness = len(dead_configs) == 0
    if not liveness:
        return {
            'valid': False,
            'properties': {'liveness': (False, f'{len(dead_configs)} dead configs')},
        }

    # Find configurations with exactly one privileged processor (candidates for good)
    single_priv = {c for c in configs if len(priv_map[c]) == 1}

    # Build transition graph restricted to single-privilege configs
    # Good configs must form a Hamiltonian cycle on single_priv (or a subset)
    # that satisfies closure, convergence, and fairness.

    # Actually, let's think about this differently.
    # We need to find a partition into good/bad such that:
    # - Good configs have exactly 1 privileged processor (mutual exclusion)
    # - Moves from good -> good (closure)
    # - No bad cycles (convergence)
    # - Good cycle visits all processors (fairness)

    # The good configs must be a subset of single_priv.
    # Each good config c has exactly one privileged processor i, so there's
    # exactly one successor: apply_move(c, i, fs, ms).
    # Closure says this successor must also be in good.
    # So good configs form a functional graph (each node has out-degree 1).
    # A functional graph's connected components are rho-shaped (tail + cycle).
    # Closure + the need for the system to keep running means good configs
    # must form cycles (no tails — a tail would lead to a config that's
    # revisited, which is fine, but the tail configs would need predecessors
    # from bad configs, which is ok).
    # Actually: closure just means good->good. So good is closed under the
    # deterministic successor map. The good set forms a functional graph
    # that could have tails leading into cycles.
    # But fairness requires every cycle through good configs visits all processors.
    # If there are multiple cycles, fairness would fail (a cycle not visiting
    # some processor). So good must contain exactly one cycle.
    # Configs on tails feeding into the cycle would also be good (closure holds
    # since their successors are good), but then the system starting on a tail
    # config would eventually enter the cycle and stay there — fairness is about
    # the cycle itself.

    # Actually, re-reading the problem: fairness says every CYCLE of moves
    # through good configurations includes a move by each processor.
    # So we need: the unique cycle in the good functional graph visits all n processors.

    # And convergence: no cycle exists among bad configurations. Since each bad
    # config can have multiple successors (multiple privileged processors,
    # daemon chooses), we need that no matter what choices the daemon makes
    # from bad configs, it can't cycle forever. This is the hardest property.
    # Equivalently: in the bad-config transition graph (where edges go from
    # each bad config to ALL its possible successors), there is no cycle.
    # Wait — convergence says no SEQUENCE of moves from bad configs cycles.
    # That means: in the nondeterministic transition graph restricted to bad
    # configs, there are no cycles. I.e., every path from a bad config
    # eventually reaches a good config regardless of daemon choices.

    # Strategy: find maximal closed subset of single_priv under the
    # deterministic successor map. This gives candidate good sets.
    # Then check convergence on the complement.

    # Build deterministic successor map on single_priv
    succ = {}
    for c in single_priv:
        i = priv_map[c][0]
        s = apply_move(c, i, fs, ms)
        succ[c] = (s, i)  # (successor config, which processor moved)

    # Find all configs in single_priv whose successor is also in single_priv
    # Iteratively remove configs whose successor leaves single_priv
    good_candidates = set(single_priv)
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for c in good_candidates:
            s, _ = succ[c]
            if s not in good_candidates:
                to_remove.add(c)
        if to_remove:
            good_candidates -= to_remove
            changed = True

    if not good_candidates:
        return {
            'valid': False,
            'properties': {
                'liveness': (True, ''),
                'mutual_exclusion_closure': (False, 'no closed set of single-privilege configs'),
            },
        }

    # Find cycles in good_candidates
    # Since it's a functional graph (each node has exactly one successor in the set),
    # find all cycles
    visited = set()
    cycles = []
    for c in good_candidates:
        if c in visited:
            continue
        path = []
        node = c
        path_set = set()
        while node not in visited and node not in path_set:
            path.append(node)
            path_set.add(node)
            node = succ[node][0]
        if node in path_set:
            # Found a cycle
            cycle_start = path.index(node)
            cycle = path[cycle_start:]
            cycles.append(cycle)
        visited.update(path)

    if not cycles:
        return {
            'valid': False,
            'properties': {
                'liveness': (True, ''),
                'mutual_exclusion_closure': (False, 'no cycle in good configs'),
            },
        }

    # Try each cycle as THE good cycle, with its basin as good set
    best_result = None
    for cycle in cycles:
        cycle_set = set(cycle)

        # The good set = cycle + all tails leading into cycle
        good = set()
        # BFS backwards from cycle through good_candidates
        # Build reverse map
        rev = defaultdict(list)
        for c in good_candidates:
            s, _ = succ[c]
            rev[s].append(c)

        queue = list(cycle_set)
        good = set(cycle_set)
        while queue:
            node = queue.pop()
            for pred in rev[node]:
                if pred not in good:
                    good.add(pred)
                    queue.append(pred)

        # Check fairness: cycle visits all n processors
        processors_in_cycle = set()
        for c in cycle:
            _, i = succ[c]
            processors_in_cycle.add(i)
        fair = processors_in_cycle == set(range(n))
        if not fair:
            continue

        # Check convergence: no cycle in bad configs under nondeterministic transitions
        bad = set(configs) - good
        # Build nondeterministic transition graph on bad configs
        # For each bad config, compute all successors (one per privileged processor)
        # Check for cycles using DFS

        # First, compute successors restricted to bad
        bad_succs = defaultdict(list)
        for c in bad:
            for i in priv_map[c]:
                s = apply_move(c, i, fs, ms)
                if s in bad:
                    bad_succs[c].append(s)

        # Check for cycles in the bad subgraph
        # Use iterative DFS with coloring (white=0, gray=1, black=2)
        color = {c: 0 for c in bad}
        has_bad_cycle = False
        for start in bad:
            if color[start] != 0:
                continue
            stack = [(start, False)]
            while stack:
                node, returning = stack.pop()
                if returning:
                    color[node] = 2
                    continue
                if color[node] == 1:
                    color[node] = 2
                    continue
                if color[node] == 2:
                    continue
                color[node] = 1
                stack.append((node, True))
                for s in bad_succs[node]:
                    if color[s] == 1:
                        has_bad_cycle = True
                        break
                    if color[s] == 0:
                        stack.append((s, False))
                if has_bad_cycle:
                    break
            if has_bad_cycle:
                break

        if has_bad_cycle:
            continue

        # All properties satisfied!
        result = {
            'valid': True,
            'properties': {
                'liveness': (True, ''),
                'mutual_exclusion': (True, f'{len(good)} good configs'),
                'closure': (True, ''),
                'convergence': (True, f'{len(bad)} bad configs, no cycles'),
                'fairness': (True, f'cycle length {len(cycle)}, all {n} processors visited'),
            },
            'good_configs': good,
            'cycle': cycle,
            'cycle_length': len(cycle),
        }
        return result

    return {
        'valid': False,
        'properties': {
            'liveness': (True, ''),
            'mutual_exclusion_closure': (True, f'{len(cycles)} candidate cycles'),
            'fairness_or_convergence': (False, 'no cycle satisfies both fairness and convergence'),
        },
    }


def verify_dijkstra_solution3(n: int, verbose: bool = False) -> dict:
    """Verify Dijkstra's Solution 3 for a ring of n processors."""
    ms = [3] * n

    def f_bottom(L, S, R):
        if (S + 1) % 3 == R:
            return (S - 1) % 3
        return S

    def f_top(L, S, R):
        if L == R and (L + 1) % 3 != S:
            return (L + 1) % 3
        return S

    def f_middle(L, S, R):
        if (S + 1) % 3 == L:
            return L
        if (S + 1) % 3 == R:
            return R
        return S

    fs = [f_bottom] + [f_middle] * (n - 2) + [f_top]
    return verify_system(ms, fs, verbose)


def verify_dijkstra_solution1(n: int, K: int, verbose: bool = False) -> dict:
    """Verify Dijkstra's Solution 1 for a ring of n processors with K states."""
    ms = [K] * n

    def f_distinguished(L, S, R):
        if L == S:
            return (S + 1) % K
        return S

    def f_other(L, S, R):
        if L != S:
            return L
        return S

    fs = [f_distinguished] + [f_other] * (n - 1)
    return verify_system(ms, fs, verbose)


def search_optimal(n: int, max_product: int = None, verbose: bool = False):
    """
    Search for the minimum state product for n processors.

    Enumerates state vectors (m_0, ..., m_{n-1}) with product <= max_product,
    and for each, exhaustively searches over all possible transition functions.

    WARNING: This is extremely expensive. The number of transition functions
    for processor i is m_i^(m_{i-1} * m_i * m_{i+1}), which grows very fast.

    For practical use, we need structural constraints to prune the search.
    """
    if max_product is None:
        max_product = 3 ** n

    # Generate candidate state vectors sorted by product
    candidates = []
    _gen_state_vectors(n, 0, [], max_product, candidates)
    candidates.sort(key=lambda v: (product(v), v))

    print(f"Searching {len(candidates)} state vectors for n={n}, max_product={max_product}")

    for ms in candidates:
        p = product(ms)
        if verbose:
            print(f"  Trying ms={ms}, product={p}")
        # Count total transition functions
        total_fns = 1
        for i in range(n):
            m_L = ms[(i - 1) % n]
            m_S = ms[i]
            m_R = ms[(i + 1) % n]
            num_inputs = m_L * m_S * m_R
            total_fns *= m_S ** num_inputs
        if verbose:
            print(f"    Total transition function space: {total_fns}")
        if total_fns > 10**8:
            if verbose:
                print(f"    SKIPPING (too large)")
            continue
        # This is still too large for brute force in most cases
        # We need smarter approaches

    return None


def product(v):
    p = 1
    for x in v:
        p *= x
    return p


def _gen_state_vectors(n, idx, current, max_product, results):
    """Generate all state vectors with product <= max_product, m_i >= 2."""
    if idx == n:
        results.append(tuple(current))
        return
    remaining = n - idx
    current_product = product(current) if current else 1
    for m in range(2, max_product + 1):
        new_product = current_product * m
        # Remaining processors need at least 2 states each
        if new_product * (2 ** (remaining - 1)) > max_product:
            break
        _gen_state_vectors(n, idx + 1, current + [m], max_product, results)


if __name__ == "__main__":
    print("=== Verifying Dijkstra's Solution 3 ===")
    for n in range(3, 8):
        result = verify_dijkstra_solution3(n)
        status = "VALID" if result['valid'] else "INVALID"
        print(f"  n={n}: {status}")
        if result['valid']:
            print(f"    Cycle length: {result['cycle_length']}")
            for prop, (ok, info) in result['properties'].items():
                if info:
                    print(f"    {prop}: {info}")

    print("\n=== Verifying Dijkstra's Solution 1 ===")
    for n in range(3, 7):
        K = n + 1
        result = verify_dijkstra_solution1(n, K)
        status = "VALID" if result['valid'] else "INVALID"
        print(f"  n={n}, K={K}: {status}")
        if result['valid']:
            print(f"    Cycle length: {result['cycle_length']}")

    print("\n=== Gray code verification for n=3,4 ===")
    # For n=3, the Gray code gives a Hamiltonian cycle on {0,1}^3
    # All 8 configs are good, each with exactly one privileged processor
    for n in [3, 4]:
        ms = [2] * n

        # Build Gray code transition functions
        # Gray code: config -> next config differs in exactly one bit
        # We need to define f_i such that the Gray code cycle is the good cycle
        if n == 3:
            # Gray code: 000->001->011->010->110->111->101->100->000
            gray_cycle = [
                (0,0,0), (0,0,1), (0,1,1), (0,1,0),
                (1,1,0), (1,1,1), (1,0,1), (1,0,0)
            ]
        elif n == 4:
            # Standard 4-bit Gray code
            gray_cycle = []
            for i in range(16):
                g = i ^ (i >> 1)
                gray_cycle.append(tuple((g >> (n-1-j)) & 1 for j in range(n)))

        # Build transition function from the cycle
        # For each config in the cycle, exactly one bit flips to get to next
        succ_map = {}
        for idx in range(len(gray_cycle)):
            c = gray_cycle[idx]
            c_next = gray_cycle[(idx + 1) % len(gray_cycle)]
            succ_map[c] = c_next

        # Find which processor moves at each step
        move_map = {}
        for idx in range(len(gray_cycle)):
            c = gray_cycle[idx]
            c_next = gray_cycle[(idx + 1) % len(gray_cycle)]
            for j in range(n):
                if c[j] != c_next[j]:
                    move_map[c] = j
                    break

        # Build f_i: for each processor i, define f_i(L, S, R)
        # If config c has processor i privileged, then f_i(L,S,R) should flip S
        # Otherwise f_i(L,S,R) = S
        fs = []
        for i in range(n):
            lookup = {}
            for c in gray_cycle:
                L = c[(i-1) % n]
                S = c[i]
                R = c[(i+1) % n]
                key = (L, S, R)
                if move_map[c] == i:
                    lookup[key] = 1 - S  # flip
                else:
                    if key not in lookup:
                        lookup[key] = S  # don't move

            def make_f(lookup_table, proc_idx):
                def f(L, S, R):
                    key = (L, S, R)
                    if key in lookup_table:
                        return lookup_table[key]
                    return S  # default: don't move
                return f

            fs.append(make_f(lookup, i))

        result = verify_system(ms, fs)
        status = "VALID" if result['valid'] else "INVALID"
        print(f"  n={n}, Gray code: {status}")
        if result['valid']:
            print(f"    Product = {2**n}, cycle length = {result['cycle_length']}")
        else:
            print(f"    Properties: {result['properties']}")
