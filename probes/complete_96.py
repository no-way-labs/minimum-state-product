"""
Complete a good cycle into a full valid system using Z3 for the unforced entries.

Given a cycle that determines some transition function entries, use SMT to
find values for the remaining entries that ensure:
1. Liveness (all configs have a privileged processor)
2. Convergence (no bad-config cycles)
"""

import z3
import itertools
import time
from typing import List, Tuple, Optional, Dict
from collections import defaultdict
from verifier import verify_system
from search_96 import enumerate_good_cycles


def complete_with_smt(ms: List[int], cycle: list, timeout_ms: int = 30000,
                      verbose: bool = False) -> Optional[dict]:
    """
    Complete a good cycle into a valid self-stabilizing system using Z3.
    """
    n = len(ms)
    total = 1
    for m in ms:
        total *= m

    cycle_tuples = [tuple(c) for c in cycle]
    cycle_set = set(cycle_tuples)

    # Extract forced assignments from the cycle
    forced = {}  # (proc, L, S, R) -> output
    for idx in range(len(cycle_tuples)):
        c = cycle_tuples[idx]
        c_next = cycle_tuples[(idx + 1) % len(cycle_tuples)]

        mover = None
        for j in range(n):
            if c[j] != c_next[j]:
                mover = j
                break

        for proc in range(n):
            view = (c[(proc-1)%n], c[proc], c[(proc+1)%n])
            key = (proc,) + view
            if proc == mover:
                forced[key] = c_next[proc]
            else:
                forced[key] = c[proc]

    # Build Z3 variables for unforced entries
    solver = z3.Solver()
    solver.set("timeout", timeout_ms)

    f = {}
    free_count = 0
    for i in range(n):
        m_L = ms[(i - 1) % n]
        m_S = ms[i]
        m_R = ms[(i + 1) % n]
        for l in range(m_L):
            for s in range(m_S):
                for r in range(m_R):
                    key = (i, l, s, r)
                    if key in forced:
                        f[key] = z3.IntVal(forced[key])
                    else:
                        var = z3.Int(f"f_{i}_{l}_{s}_{r}")
                        f[key] = var
                        solver.add(var >= 0, var < ms[i])
                        free_count += 1

    all_configs = list(itertools.product(*(range(m) for m in ms)))
    bad_configs = [c for c in all_configs if c not in cycle_set]

    # Liveness on bad configs (cycle configs already have it by construction)
    for c in bad_configs:
        priv_clauses = []
        for i in range(n):
            l, s, r = c[(i-1)%n], c[i], c[(i+1)%n]
            priv_clauses.append(f[(i, l, s, r)] != s)
        solver.add(z3.Or(*priv_clauses))

    # Convergence: ranking function on bad configs
    rank = {}
    num_bad = len(bad_configs)
    for c in bad_configs:
        rank[c] = z3.Int(f"r_{all_configs.index(c)}")
        solver.add(rank[c] >= 0, rank[c] < num_bad)

    for c in bad_configs:
        for i in range(n):
            l, s, r = c[(i-1)%n], c[i], c[(i+1)%n]
            fval = f[(i, l, s, r)]
            for new_s in range(ms[i]):
                if new_s == s:
                    continue
                succ = list(c)
                succ[i] = new_s
                succ = tuple(succ)

                cond = z3.And(fval == new_s)

                if succ in cycle_set:
                    # Bad -> good: fine, no constraint
                    pass
                else:
                    # Bad -> bad: rank must decrease
                    solver.add(z3.Implies(cond, rank[succ] < rank[c]))

    result = solver.check()

    if result == z3.sat:
        model = solver.model()
        fs_values = {}
        for key, var in f.items():
            if z3.is_int_value(var):
                fs_values[key] = var.as_long()
            else:
                fs_values[key] = model[var].as_long()

        def make_f(proc, values):
            def func(L, S, R):
                return values[(proc, L, S, R)]
            return func

        fs_list = [make_f(i, fs_values) for i in range(n)]
        verification = verify_system(ms, fs_list)

        if verification['valid']:
            return {
                'ms': ms,
                'product': total,
                'cycle': cycle_tuples,
                'cycle_length': len(cycle_tuples),
                'fs_values': fs_values,
                'verification': verification,
                'free_entries': free_count,
            }

    return None


def search_product_96_smt(verbose: bool = True):
    """Search product 96 using good-cycle enumeration + SMT completion."""
    from smt_search import has_four_consecutive_binary, canonical_rotation

    vectors = [
        [2, 2, 2, 3, 4],
        [2, 2, 3, 2, 4],
        [2, 2, 2, 4, 3],
        [2, 2, 4, 2, 3],
    ]

    for ms in vectors:
        if verbose:
            print(f"=== ms={ms}, product=96 ===")

        cycles = enumerate_good_cycles(ms, max_cycles=500, verbose=False)
        if verbose:
            print(f"  Found {len(cycles)} good cycles")
            if cycles:
                lengths = [len(c) for c in cycles]
                print(f"  Cycle lengths: min={min(lengths)}, max={max(lengths)}, "
                      f"median={sorted(lengths)[len(lengths)//2]}")

        for i, cycle in enumerate(cycles):
            result = complete_with_smt(ms, cycle, timeout_ms=10000, verbose=False)
            if result:
                if verbose:
                    print(f"  VALID! Cycle #{i+1} (len={len(cycle)}), "
                          f"verified cycle_len={result['verification']['cycle_length']}, "
                          f"free_entries={result['free_entries']}")
                return result

            if (i + 1) % 50 == 0 and verbose:
                print(f"  Tested {i+1}/{len(cycles)} cycles...")

        if verbose:
            print(f"  No valid completion found")
            print()

    return None


if __name__ == "__main__":
    print("=" * 60)
    print("PRODUCT 96 SEARCH: Good-cycle + SMT completion")
    print("=" * 60)
    print()

    result = search_product_96_smt(verbose=True)

    if result:
        print(f"\n{'='*60}")
        print(f"VERIFIED: M_5 <= 96")
        print(f"ms={result['ms']}, cycle_length={result['cycle_length']}")
        print(f"Full verification: {result['verification']['properties']}")
        print(f"{'='*60}")

        # Print transition functions
        print("\nTransition functions:")
        n = len(result['ms'])
        for i in range(n):
            print(f"\n  Processor {i} ({result['ms'][i]}-state):")
            m_L = result['ms'][(i-1) % n]
            m_S = result['ms'][i]
            m_R = result['ms'][(i+1) % n]
            for l in range(m_L):
                for s in range(m_S):
                    for r in range(m_R):
                        val = result['fs_values'][(i, l, s, r)]
                        priv = " *" if val != s else ""
                        print(f"    f({l},{s},{r}) = {val}{priv}")

        # Save
        with open("product96_result.txt", "w") as fout:
            fout.write(f"ms={result['ms']}\n")
            fout.write(f"product=96\n")
            fout.write(f"cycle_length={result['cycle_length']}\n")
            fout.write(f"good_cycle={result['cycle']}\n\n")
            for key, val in sorted(result['fs_values'].items()):
                fout.write(f"f[{key[0]}]({key[1]},{key[2]},{key[3]}) = {val}\n")
    else:
        print("\nFailed to find product 96 construction with current approach.")
        print("May need more cycles or different starting configs.")
