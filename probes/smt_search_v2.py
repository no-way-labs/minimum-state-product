"""
SMT-based search v2: CEGAR loop + stronger cycle encoding.

Strategy:
1. Encode transition functions as Z3 integer variables
2. Encode liveness as hard constraint
3. Encode single-cycle structure using position variables
4. Verify with exact verifier, add blocking clauses on failure
"""

import z3
import itertools
import sys
import time
from typing import List, Tuple, Optional, Set
from verifier import verify_system, privileged_set, apply_move


def search_v2(ms: List[int], timeout_ms: int = 120000, max_iters: int = 100,
              verbose: bool = True) -> Optional[dict]:
    """
    SMT search with CEGAR loop.
    """
    n = len(ms)
    total = 1
    for m in ms:
        total *= m

    if verbose:
        print(f"Searching ms={ms}, product={total}")

    solver = z3.Solver()
    solver.set("timeout", timeout_ms)

    # Transition function variables
    f = {}
    for i in range(n):
        m_L = ms[(i - 1) % n]
        m_S = ms[i]
        m_R = ms[(i + 1) % n]
        for l in range(m_L):
            for s in range(m_S):
                for r in range(m_R):
                    var = z3.Int(f"f_{i}_{l}_{s}_{r}")
                    f[(i, l, s, r)] = var
                    solver.add(var >= 0, var < ms[i])

    # All configurations
    configs = list(itertools.product(*(range(m) for m in ms)))

    # Liveness: every config has at least one privileged processor
    for c in configs:
        priv_clauses = []
        for i in range(n):
            l, s, r = c[(i-1)%n], c[i], c[(i+1)%n]
            priv_clauses.append(f[(i, l, s, r)] != s)
        solver.add(z3.Or(*priv_clauses))

    iteration = 0
    while iteration < max_iters:
        iteration += 1
        if verbose:
            print(f"  Iteration {iteration}...")

        result = solver.check()

        if result == z3.unsat:
            if verbose:
                print(f"  UNSAT after {iteration} iterations")
            return None
        elif result == z3.unknown:
            if verbose:
                print(f"  Timeout/unknown after {iteration} iterations")
            return None

        # Extract model
        model = solver.model()
        fs_values = {}
        for (i, l, s, r), var in f.items():
            fs_values[(i, l, s, r)] = model[var].as_long()

        # Build transition functions
        def make_f(proc_idx, values):
            def func(L, S, R):
                return values.get((proc_idx, L, S, R), S)
            return func

        fs_list = [make_f(i, fs_values) for i in range(n)]

        # Verify
        verification = verify_system(ms, fs_list)

        if verification['valid']:
            if verbose:
                print(f"  VALID system found! Cycle length: {verification['cycle_length']}")
            return {
                'ms': ms,
                'product': total,
                'fs_values': fs_values,
                'verification': verification,
            }

        # Add blocking clause: exclude this exact transition function assignment
        block = []
        for (i, l, s, r), val in fs_values.items():
            block.append(f[(i, l, s, r)] != val)
        solver.add(z3.Or(*block))

        if verbose and iteration <= 5:
            props = verification['properties']
            reasons = [f"{k}: {v[1]}" for k, v in props.items() if not v[0]]
            print(f"    Failed: {'; '.join(reasons)}")

    if verbose:
        print(f"  Exhausted {max_iters} iterations")
    return None


def search_v2_structural(ms: List[int], timeout_ms: int = 120000,
                         verbose: bool = True) -> Optional[dict]:
    """
    Structural SMT search: encode single-cycle property directly.

    Use cycle position variables to enforce that good configs form exactly
    one cycle of length L, visiting all processors.
    """
    n = len(ms)
    total = 1
    for m in ms:
        total *= m

    if verbose:
        print(f"Structural search ms={ms}, product={total}")

    configs = list(itertools.product(*(range(m) for m in ms)))
    config_idx = {c: i for i, c in enumerate(configs)}

    # Try different cycle lengths
    # Minimum: n (each processor moves at least once)
    # Maximum: total (all configs in cycle, like Gray code)
    # Dijkstra S3 has cycle length 6(n-1)=24 for n=5

    for cycle_len in range(n, total + 1):
        if verbose and cycle_len <= n + 5:
            print(f"  Trying cycle_len={cycle_len}...")

        solver = z3.Solver()
        solver.set("timeout", timeout_ms // 10)  # distribute timeout

        # Transition function variables
        f = {}
        for i in range(n):
            m_L = ms[(i - 1) % n]
            m_S = ms[i]
            m_R = ms[(i + 1) % n]
            for l in range(m_L):
                for s in range(m_S):
                    for r in range(m_R):
                        var = z3.Int(f"f_{i}_{l}_{s}_{r}")
                        f[(i, l, s, r)] = var
                        solver.add(var >= 0, var < ms[i])

        # Cycle config variables: cycle[t] is the config at position t
        # Encode as n integer variables per position
        cycle_vars = []
        for t in range(cycle_len):
            pos = []
            for j in range(n):
                v = z3.Int(f"c_{t}_{j}")
                solver.add(v >= 0, v < ms[j])
                pos.append(v)
            cycle_vars.append(pos)

        # Which processor moves at position t
        mover = []
        for t in range(cycle_len):
            v = z3.Int(f"mv_{t}")
            solver.add(v >= 0, v < n)
            mover.append(v)

        # Transition constraint: cycle[t+1] = cycle[t] with position mover[t] updated
        for t in range(cycle_len):
            t_next = (t + 1) % cycle_len
            for j in range(n):
                for i_val in range(n):
                    if i_val == j:
                        # If mover[t] == j, then cycle[t+1][j] = f_j(cycle[t][j-1], cycle[t][j], cycle[t][j+1])
                        # This is complex... cycle[t][j-1] etc are variables
                        pass
                    else:
                        # If mover[t] != j, then cycle[t+1][j] = cycle[t][j]
                        solver.add(z3.Implies(mover[t] != j, cycle_vars[t_next][j] == cycle_vars[t][j]))

            # For the mover: cycle[t+1][mover[t]] = f_{mover[t]}(L, S, R)
            for i_val in range(n):
                l_idx = (i_val - 1) % n
                r_idx = (i_val + 1) % n
                # When mover[t] == i_val:
                # Need: cycle_vars[t_next][i_val] = f[i_val](cycle_vars[t][l_idx], cycle_vars[t][i_val], cycle_vars[t][r_idx])
                # And: f[i_val](...) != cycle_vars[t][i_val] (privileged)

                for l_v in range(ms[l_idx]):
                    for s_v in range(ms[i_val]):
                        for r_v in range(ms[r_idx]):
                            cond = z3.And(
                                mover[t] == i_val,
                                cycle_vars[t][l_idx] == l_v,
                                cycle_vars[t][i_val] == s_v,
                                cycle_vars[t][r_idx] == r_v
                            )
                            solver.add(z3.Implies(cond,
                                cycle_vars[t_next][i_val] == f[(i_val, l_v, s_v, r_v)]))
                            # Privileged: f != S
                            solver.add(z3.Implies(cond,
                                f[(i_val, l_v, s_v, r_v)] != s_v))

        # Mutual exclusion on cycle: only the mover is privileged
        for t in range(cycle_len):
            for j in range(n):
                # If mover[t] != j, then processor j is NOT privileged at cycle[t]
                for l_v in range(ms[(j-1)%n]):
                    for s_v in range(ms[j]):
                        for r_v in range(ms[(j+1)%n]):
                            cond = z3.And(
                                mover[t] != j,
                                cycle_vars[t][(j-1)%n] == l_v,
                                cycle_vars[t][j] == s_v,
                                cycle_vars[t][(j+1)%n] == r_v
                            )
                            solver.add(z3.Implies(cond, f[(j, l_v, s_v, r_v)] == s_v))

        # All configs in cycle are distinct
        for t1 in range(cycle_len):
            for t2 in range(t1 + 1, cycle_len):
                solver.add(z3.Or(*[cycle_vars[t1][j] != cycle_vars[t2][j] for j in range(n)]))

        # Fairness: every processor appears as mover at least once
        for i_val in range(n):
            solver.add(z3.Or(*[mover[t] == i_val for t in range(cycle_len)]))

        # Liveness on ALL configs (not just cycle)
        for c in configs:
            priv_clauses = []
            for i in range(n):
                l, s, r = c[(i-1)%n], c[i], c[(i+1)%n]
                priv_clauses.append(f[(i, l, s, r)] != s)
            solver.add(z3.Or(*priv_clauses))

        # Convergence: for non-cycle configs, all paths lead to cycle
        # This is still hard to encode... skip for now and verify post-hoc

        result = solver.check()

        if result == z3.sat:
            model = solver.model()

            # Extract transition functions
            fs_values = {}
            for (i, l, s, r), var in f.items():
                fs_values[(i, l, s, r)] = model[var].as_long()

            def make_f(proc_idx, values):
                def func(L, S, R):
                    return values.get((proc_idx, L, S, R), S)
                return func

            fs_list = [make_f(i, fs_values) for i in range(n)]

            # Extract cycle
            cycle_configs = []
            for t in range(cycle_len):
                cfg = tuple(model[cycle_vars[t][j]].as_long() for j in range(n))
                cycle_configs.append(cfg)

            if verbose:
                print(f"    Z3 found candidate with cycle_len={cycle_len}")
                print(f"    Cycle: {cycle_configs[:5]}...")

            # Full verification
            verification = verify_system(ms, fs_list)

            if verification['valid']:
                if verbose:
                    print(f"    VERIFIED! Cycle length: {verification['cycle_length']}")
                return {
                    'ms': ms,
                    'product': total,
                    'fs_values': fs_values,
                    'verification': verification,
                    'cycle': cycle_configs,
                }
            else:
                if verbose:
                    print(f"    Verification failed: {verification['properties']}")
                # Could add blocking clauses, but for now continue to next cycle length
        elif result == z3.unknown:
            if verbose:
                print(f"    Timeout at cycle_len={cycle_len}")
            # Skip to larger cycle lengths (they'll also timeout)
            break

    return None


def search_cegar(ms: List[int], timeout_ms: int = 300000, max_iters: int = 1000,
                 verbose: bool = True) -> Optional[dict]:
    """
    CEGAR-style search with incremental constraint strengthening.

    Core idea: start with weak constraints (liveness only), find a model,
    verify all properties, add targeted constraints for failures, repeat.
    """
    n = len(ms)
    total = 1
    for m in ms:
        total *= m

    if verbose:
        print(f"CEGAR search ms={ms}, product={total}")

    solver = z3.Solver()
    solver.set("timeout", timeout_ms)

    configs = list(itertools.product(*(range(m) for m in ms)))
    config_idx = {c: i for i, c in enumerate(configs)}

    # Transition function variables
    f = {}
    for i in range(n):
        m_L = ms[(i - 1) % n]
        m_S = ms[i]
        m_R = ms[(i + 1) % n]
        for l in range(m_L):
            for s in range(m_S):
                for r in range(m_R):
                    var = z3.Int(f"f_{i}_{l}_{s}_{r}")
                    f[(i, l, s, r)] = var
                    solver.add(var >= 0, var < ms[i])

    # Liveness
    for c in configs:
        priv_clauses = []
        for i in range(n):
            l, s, r = c[(i-1)%n], c[i], c[(i+1)%n]
            priv_clauses.append(f[(i, l, s, r)] != s)
        solver.add(z3.Or(*priv_clauses))

    # Also add: there must exist configs with exactly one privileged processor
    # (otherwise no good configs possible)

    iteration = 0
    start_time = time.time()
    best_failure = None

    while iteration < max_iters:
        iteration += 1
        elapsed = time.time() - start_time
        if elapsed > timeout_ms / 1000:
            break

        result = solver.check()

        if result == z3.unsat:
            if verbose:
                print(f"  UNSAT after {iteration} iterations ({elapsed:.1f}s)")
                if best_failure:
                    print(f"  Best failure reason: {best_failure}")
            return None
        elif result == z3.unknown:
            if verbose:
                print(f"  Timeout after {iteration} iterations ({elapsed:.1f}s)")
            return None

        model = solver.model()
        fs_values = {}
        for (i, l, s, r), var in f.items():
            fs_values[(i, l, s, r)] = model[var].as_long()

        def make_f(proc_idx, values):
            def func(L, S, R):
                return values.get((proc_idx, L, S, R), S)
            return func

        fs_list = [make_f(i, fs_values) for i in range(n)]

        verification = verify_system(ms, fs_list)

        if verification['valid']:
            if verbose:
                print(f"  VALID! iteration={iteration}, cycle_len={verification['cycle_length']} ({elapsed:.1f}s)")
            return {
                'ms': ms,
                'product': total,
                'fs_values': fs_values,
                'verification': verification,
            }

        # Analyze failure and add targeted constraints
        props = verification['properties']

        # Blocking clause for this exact assignment
        block = []
        for (i, l, s, r), val in fs_values.items():
            block.append(f[(i, l, s, r)] != val)
        solver.add(z3.Or(*block))

        # Additional targeted constraints based on failure type
        if 'fairness_or_convergence' in props and not props['fairness_or_convergence'][0]:
            # Try to add structural hints
            pass

        if iteration <= 3 and verbose:
            reasons = {k: v[1] for k, v in props.items() if not v[0]}
            print(f"  iter {iteration}: failed - {reasons}")
            best_failure = reasons

        if iteration % 100 == 0 and verbose:
            print(f"  iter {iteration} ({elapsed:.1f}s)...")

    if verbose:
        print(f"  Exhausted {iteration} iterations")
    return None


if __name__ == "__main__":
    from smt_search import generate_state_vectors, canonical_rotation, has_four_consecutive_binary, prod

    n = 5
    max_product = 3 ** n

    all_vectors = generate_state_vectors(n, max_product - 1)
    seen = set()
    vectors = []
    for v in all_vectors:
        canon = canonical_rotation(v)
        if canon not in seen:
            seen.add(canon)
            vectors.append(v)
    feasible = [v for v in vectors if not has_four_consecutive_binary(list(v))]

    by_product = {}
    for v in feasible:
        p = prod(v)
        if p not in by_product:
            by_product[p] = []
        by_product[p].append(v)

    print(f"=== CEGAR Search for M_{n} ===")
    print(f"Known: {2**n} < M_{n} <= {3**n}")
    print()

    for p in sorted(by_product.keys()):
        vecs = by_product[p]
        for v in vecs:
            result = search_cegar(list(v), timeout_ms=60000, max_iters=500, verbose=True)
            if result:
                print(f"\n*** FOUND: product={p}, ms={v} ***")
                print(f"Cycle length: {result['verification']['cycle_length']}")
                with open("search_results.txt", "a") as fout:
                    fout.write(f"ms={v}, product={p}, cycle_len={result['verification']['cycle_length']}\n")
                    for key, val in sorted(result['fs_values'].items()):
                        fout.write(f"  f[{key[0]}]({key[1]},{key[2]},{key[3]}) = {val}\n")
                    fout.write("\n")
                sys.exit(0)
            print()
