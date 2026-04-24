"""
SMT-based search for minimum-product self-stabilizing token rings.

Encodes all 5 Dijkstra properties as Z3 constraints:
1. Liveness: every config has at least one privileged processor
2. Mutual exclusion: good configs have exactly one privileged processor
3. Closure: deterministic successor of good config is good
4. Convergence: no bad-config cycle (via ranking function)
5. Fairness: good cycle visits all processors

Variables:
- f[i][l][s][r]: transition function output for processor i seeing (l,s,r)
- good[c]: whether config c is a good config
- rank[c]: ranking value for convergence proof (bad configs decrease rank)
"""

import z3
import itertools
import sys
import time
from typing import List, Tuple, Optional


def config_to_idx(config: Tuple[int, ...], ms: List[int]) -> int:
    """Convert configuration tuple to integer index."""
    idx = 0
    for i, (c, m) in enumerate(zip(config, ms)):
        idx = idx * m + c
    return idx


def idx_to_config(idx: int, ms: List[int]) -> Tuple[int, ...]:
    """Convert integer index to configuration tuple."""
    config = []
    for m in reversed(ms):
        config.append(idx % m)
        idx //= m
    return tuple(reversed(config))


def search_smt(ms: List[int], timeout_ms: int = 60000, verbose: bool = True) -> Optional[dict]:
    """
    Search for a self-stabilizing token ring with given state vector.

    Returns dict with transition functions if found, None otherwise.
    """
    n = len(ms)
    total = 1
    for m in ms:
        total *= m

    if verbose:
        print(f"Searching ms={ms}, product={total}, n={n}")

    solver = z3.Solver()
    solver.set("timeout", timeout_ms)

    # Transition function variables: f[i][(l,s,r)] -> output value in [0, m_i-1]
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

    # Helper: is processor i privileged in config c?
    def is_priv(config, i):
        l = config[(i - 1) % n]
        s = config[i]
        r = config[(i + 1) % n]
        return f[(i, l, s, r)] != s

    # Helper: new state of processor i after moving in config c
    def new_state(config, i):
        l = config[(i - 1) % n]
        s = config[i]
        r = config[(i + 1) % n]
        return f[(i, l, s, r)]

    # Generate all configurations
    configs = list(itertools.product(*(range(m) for m in ms)))
    config_idx = {c: i for i, c in enumerate(configs)}

    # Good/bad partition: good[c] is a Bool
    good = {}
    for c in configs:
        good[c] = z3.Bool(f"good_{config_idx[c]}")

    # Ranking for convergence: rank[c] for bad configs
    rank = {}
    for c in configs:
        rank[c] = z3.Int(f"rank_{config_idx[c]}")
        solver.add(rank[c] >= 0, rank[c] < total)

    # === PROPERTY 1: LIVENESS ===
    # Every config has at least one privileged processor
    for c in configs:
        solver.add(z3.Or(*[is_priv(c, i) for i in range(n)]))

    # === PROPERTY 2: MUTUAL EXCLUSION ===
    # Good configs have exactly one privileged processor
    for c in configs:
        priv_vars = [is_priv(c, i) for i in range(n)]
        # If good, exactly one is privileged
        # Encode: good -> (exactly one priv)
        # exactly_one = at_least_one AND at_most_one
        at_least_one = z3.Or(*priv_vars)
        at_most_one_clauses = []
        for i in range(n):
            for j in range(i + 1, n):
                at_most_one_clauses.append(z3.Not(z3.And(priv_vars[i], priv_vars[j])))
        exactly_one = z3.And(at_least_one, *at_most_one_clauses)
        solver.add(z3.Implies(good[c], exactly_one))

    # === PROPERTY 3: CLOSURE ===
    # If c is good, its deterministic successor is also good.
    # The successor is obtained by moving the unique privileged processor.
    for c in configs:
        for i in range(n):
            # If c is good and processor i is the privileged one...
            priv_i = z3.And(good[c], is_priv(c, i),
                           *[z3.Not(is_priv(c, j)) for j in range(n) if j != i])
            # Then the successor config must be good
            # Successor: same as c except position i gets new_state(c, i)
            for new_s in range(ms[i]):
                # If f_i outputs new_s (which != c[i] since i is privileged)
                if new_s == c[i]:
                    continue
                succ = list(c)
                succ[i] = new_s
                succ = tuple(succ)
                cond = z3.And(priv_i, new_state(c, i) == new_s)
                solver.add(z3.Implies(cond, good[succ]))

    # === PROPERTY 4: CONVERGENCE ===
    # No cycle among bad configs under nondeterministic daemon.
    # Encoded via ranking: for each bad config c and each successor s (via any
    # privileged processor i), if s is also bad then rank[s] < rank[c].
    for c in configs:
        for i in range(n):
            # If c is bad and processor i is privileged, and the successor is bad
            for new_s in range(ms[i]):
                if new_s == c[i]:
                    continue
                succ = list(c)
                succ[i] = new_s
                succ = tuple(succ)
                cond = z3.And(
                    z3.Not(good[c]),
                    f[(i, c[(i-1)%n], c[i], c[(i+1)%n])] == new_s,
                    z3.Not(good[succ])
                )
                solver.add(z3.Implies(cond, rank[succ] < rank[c]))

    # === PROPERTY 5: FAIRNESS ===
    # The good cycle visits all processors.
    # This is harder to encode directly. Let's use an approach:
    # There must exist at least one good config where each processor is privileged.
    for i in range(n):
        solver.add(z3.Or(*[z3.And(good[c], is_priv(c, i),
                           *[z3.Not(is_priv(c, j)) for j in range(n) if j != i])
                          for c in configs]))

    # === Additional constraint: at least one good config ===
    solver.add(z3.Or(*[good[c] for c in configs]))

    # === Additional: good configs form a single cycle ===
    # This is implicitly handled by closure + fairness for connected systems,
    # but let's add cycle structure explicitly.
    # Each good config has exactly one good predecessor (functional graph is
    # a permutation on good configs if it's a single cycle).
    # For now, we rely on the above constraints and verify cycle structure post-hoc.

    if verbose:
        print(f"  Constraints added. Solving...")

    start = time.time()
    result = solver.check()
    elapsed = time.time() - start

    if verbose:
        print(f"  Result: {result} ({elapsed:.1f}s)")

    if result == z3.sat:
        model = solver.model()

        # Extract transition functions
        fs_values = {}
        for (i, l, s, r), var in f.items():
            fs_values[(i, l, s, r)] = model[var].as_long()

        # Extract good configs
        good_configs = set()
        for c in configs:
            if z3.is_true(model[good[c]]):
                good_configs.add(c)

        # Build actual transition functions for verification
        def make_f(proc_idx, values):
            def func(L, S, R):
                return values.get((proc_idx, L, S, R), S)
            return func

        fs_list = [make_f(i, fs_values) for i in range(n)]

        if verbose:
            print(f"  Good configs: {len(good_configs)} / {total}")
            print(f"  Verifying solution...")

        # Verify with our verifier
        from verifier import verify_system
        verification = verify_system(ms, fs_list)

        if verification['valid']:
            if verbose:
                print(f"  VERIFIED: Valid self-stabilizing system!")
                print(f"  Cycle length: {verification['cycle_length']}")
            return {
                'ms': ms,
                'product': total,
                'fs_values': fs_values,
                'good_configs': good_configs,
                'verification': verification,
            }
        else:
            if verbose:
                print(f"  WARNING: Z3 found a model but verification failed!")
                print(f"  Properties: {verification['properties']}")
            return None
    elif result == z3.unknown:
        if verbose:
            print(f"  Timeout or unknown")
        return None
    else:
        if verbose:
            print(f"  UNSAT: No valid system exists for ms={ms}")
        return None


def generate_state_vectors(n: int, max_product: int, min_state: int = 2) -> List[Tuple[int, ...]]:
    """Generate state vectors sorted by product."""
    results = []

    def recurse(idx, current, remaining_product):
        if idx == n:
            results.append(tuple(current))
            return
        remaining = n - idx
        for m in range(min_state, remaining_product + 1):
            # Check if remaining processors can fit
            if m * (min_state ** (remaining - 1)) > remaining_product:
                break
            recurse(idx + 1, current + [m], remaining_product // m if m > 0 else 0)

    # More careful generation
    def gen(idx, current, max_p):
        if idx == n:
            p = 1
            for x in current:
                p *= x
            if p <= max_product:
                results.append(tuple(current))
            return
        rem = n - idx
        for m in range(min_state, max_product + 1):
            p = 1
            for x in current:
                p *= x
            p *= m
            if p * (min_state ** (rem - 1)) > max_product:
                break
            gen(idx + 1, current + [m], max_product)

    gen(0, [], max_product)

    # Sort by product, then lexicographically
    results.sort(key=lambda v: (prod(v), v))
    return results


def prod(v):
    p = 1
    for x in v:
        p *= x
    return p


def has_four_consecutive_binary(ms: List[int]) -> bool:
    """Check if the ring has 4+ consecutive 2-state processors."""
    n = len(ms)
    # Check all starting positions for runs of 2-state processors
    for start in range(n):
        count = 0
        for offset in range(n):
            if ms[(start + offset) % n] == 2:
                count += 1
                if count >= 4:
                    return True
            else:
                break
    return False


def canonical_rotation(ms: Tuple[int, ...]) -> Tuple[int, ...]:
    """Return the lexicographically smallest rotation of ms."""
    n = len(ms)
    rotations = [tuple(ms[(i + j) % n] for j in range(n)) for i in range(n)]
    return min(rotations)


if __name__ == "__main__":
    n = 5
    max_product = 3 ** n  # 243

    print(f"=== Searching for M_{n} ===")
    print(f"Known bounds: {2**n} < M_{n} <= {3**n}")
    print()

    # Generate candidate state vectors
    all_vectors = generate_state_vectors(n, max_product - 1)  # strictly less than 3^n

    # Deduplicate by canonical rotation
    seen = set()
    vectors = []
    for v in all_vectors:
        canon = canonical_rotation(v)
        if canon not in seen:
            seen.add(canon)
            vectors.append(v)

    # Filter out impossible ones (4+ consecutive binary)
    feasible = [v for v in vectors if not has_four_consecutive_binary(list(v))]

    print(f"Total candidate vectors (product < {max_product}): {len(all_vectors)}")
    print(f"After rotation dedup: {len(vectors)}")
    print(f"After removing 4+ consecutive binary: {len(feasible)}")
    print()

    # Group by product
    by_product = {}
    for v in feasible:
        p = prod(v)
        if p not in by_product:
            by_product[p] = []
        by_product[p].append(v)

    for p in sorted(by_product.keys()):
        vecs = by_product[p]
        print(f"Product {p}: {len(vecs)} vectors")
        for v in vecs[:5]:
            print(f"  {v}")
        if len(vecs) > 5:
            print(f"  ... and {len(vecs) - 5} more")

    print()
    print("=== Starting SMT search (smallest products first) ===")
    print()

    for p in sorted(by_product.keys()):
        vecs = by_product[p]
        for v in vecs:
            result = search_smt(list(v), timeout_ms=30000, verbose=True)
            if result:
                print(f"\n*** FOUND: Valid system with product {p}, ms={v} ***\n")
                # Save result
                with open("search_results.txt", "a") as f_out:
                    f_out.write(f"ms={v}, product={p}\n")
                    f_out.write(f"Cycle length: {result['verification']['cycle_length']}\n")
                    f_out.write(f"Transition functions:\n")
                    for key, val in sorted(result['fs_values'].items()):
                        f_out.write(f"  f[{key[0]}]({key[1]},{key[2]},{key[3]}) = {val}\n")
                    f_out.write("\n")
                sys.exit(0)
            print()

    print("No valid system found with product < 3^n")
