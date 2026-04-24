"""Independently verify Sol 3 v1 witness for n=9, ms=(2,3,3,3,3,3,3,3,3), product 13122.

Builds transition tables from the rule definitions, then verifies all 5 Dijkstra properties
using both our verifier.py and docs/verify_witnesses.py.
"""

import os
import sys
from itertools import product as cartesian

sys.path.insert(0, os.path.dirname(__file__))
from verifier import verify_system


# === Rule definitions (Sol 3 "v1" — replace K with m_i) ===

def make_sol3v1_rules(state_counts):
    """Build transition functions for Sol 3 v1 with mixed state counts."""
    n = len(state_counts)

    def f_bottom(L, S, R):
        """P0 (bottom, m=state_counts[0])."""
        m = state_counts[0]
        if (S + 1) % m == R % m:
            return (S - 1) % m
        return S

    def f_top(L, S, R):
        """P_{n-1} (top, m=state_counts[n-1])."""
        m = state_counts[n - 1]
        if L % m == R % m and (L % m + 1) % m != S:
            return (L % m + 1) % m
        return S

    def make_f_middle(m):
        def f_middle(L, S, R):
            if (S + 1) % m == L % m:
                return L % m
            if (S + 1) % m == R % m:
                return R % m
            return S
        return f_middle

    fs = [f_bottom]
    for i in range(1, n - 1):
        fs.append(make_f_middle(state_counts[i]))
    fs.append(f_top)
    return fs


def build_transition_tables(state_counts, fs):
    """Convert function-based rules to lookup-table rules for docs/verify_witnesses.py."""
    n = len(state_counts)
    tables = []
    for i in range(n):
        table = {}
        m_L = state_counts[(i - 1) % n]
        m_S = state_counts[i]
        m_R = state_counts[(i + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    table[(L, S, R)] = fs[i](L, S, R)
        tables.append(table)
    return tables


def verify_with_docs_verifier(name, state_counts, tables):
    """Use the verify() function from docs/verify_witnesses.py."""
    # Import the docs verifier
    docs_path = os.path.join(os.path.dirname(__file__), "..", "docs")
    sys.path.insert(0, docs_path)
    from verify_witnesses import verify
    return verify(name, state_counts, tables)


def count_recurrent_components(state_counts, tables):
    """Count recurrent components in the single-privilege functional graph."""
    n = len(state_counts)
    configs = list(cartesian(*(range(m) for m in state_counts)))

    def privileged(cfg):
        priv = []
        for i in range(n):
            L = cfg[(i - 1) % n]
            S = cfg[i]
            R = cfg[(i + 1) % n]
            if tables[i][(L, S, R)] != S:
                priv.append(i)
        return priv

    def move(cfg, proc):
        L = cfg[(proc - 1) % n]
        S = cfg[proc]
        R = cfg[(proc + 1) % n]
        new_S = tables[proc][(L, S, R)]
        lst = list(cfg)
        lst[proc] = new_S
        return tuple(lst)

    # Build functional graph on single-privilege configs
    single_priv = {}
    for cfg in configs:
        priv = privileged(cfg)
        if len(priv) == 1:
            nxt = move(cfg, priv[0])
            single_priv[cfg] = (nxt, priv[0])

    # Find cycles
    visited = set()
    cycles = []
    for start in single_priv:
        if start in visited:
            continue
        path = []
        path_set = set()
        cur = start
        while cur in single_priv and cur not in visited and cur not in path_set:
            path.append(cur)
            path_set.add(cur)
            cur = single_priv[cur][0]
        if cur in path_set:
            idx = path.index(cur)
            cycle = path[idx:]
            cycles.append(cycle)
        visited.update(path_set)

    return len(cycles), cycles


def main():
    # === n=9 verification ===
    ms_9 = (2, 3, 3, 3, 3, 3, 3, 3, 3)
    product_9 = 1
    for m in ms_9:
        product_9 *= m

    print(f"{'='*60}")
    print(f"Sol 3 v1 verification: n=9, ms={ms_9}, product={product_9}")
    print(f"{'='*60}\n")

    fs_9 = make_sol3v1_rules(ms_9)
    tables_9 = build_transition_tables(ms_9, fs_9)

    # Print a few sample rules for sanity check
    print("Sample rule outputs:")
    print(f"  P0(L=0,S=0,R=0) = {fs_9[0](0,0,0)}  (bottom, m=2)")
    print(f"  P0(L=0,S=0,R=1) = {fs_9[0](0,0,1)}  ((S+1)%2=1 == R%2=1 → (S-1)%2=1)")
    print(f"  P1(L=0,S=0,R=0) = {fs_9[1](0,0,0)}  (middle, m=3)")
    print(f"  P1(L=0,S=0,R=1) = {fs_9[1](0,0,1)}  ((S+1)%3=1 == R%3=1 → R%3=1)")
    print(f"  P8(L=0,S=0,R=0) = {fs_9[8](0,0,0)}  (top, m=3, L%3==R%3=0, (0+1)%3=1!=0 → 1)")
    print(f"  P8(L=1,S=0,R=2) = {fs_9[8](1,0,2)}  (top, L%3=1!=R%3=2 → S=0)")
    print()

    # Verify with our verifier (function-based)
    print("--- Verification with verifier.py (function-based) ---")
    result_9 = verify_system(list(ms_9), fs_9, verbose=True)
    print(f"  Valid: {result_9['valid']}")
    if result_9['valid']:
        print(f"  Cycle length: {result_9['cycle_length']}")
        for prop, (ok, info) in result_9['properties'].items():
            status = "PASS" if ok else "FAIL"
            print(f"  {prop}: {status} {info}")
        print(f"  Good configs: {len(result_9['good_configs'])}")
        print(f"  Bad configs: {product_9 - len(result_9['good_configs'])}")
    else:
        print(f"  Properties: {result_9['properties']}")
    print()

    # Verify with docs verifier (table-based)
    print("--- Verification with docs/verify_witnesses.py (table-based) ---")
    ok_docs = verify_with_docs_verifier("n=9, Sol3v1", ms_9, tables_9)
    print()

    # Count recurrent components
    print("--- Recurrent component analysis ---")
    num_components, cycles = count_recurrent_components(ms_9, tables_9)
    print(f"  Recurrent components: {num_components}")
    for i, cyc in enumerate(cycles):
        movers = set()
        for cfg in cyc:
            priv = []
            for pi in range(len(ms_9)):
                L = cfg[(pi - 1) % len(ms_9)]
                S = cfg[pi]
                R = cfg[(pi + 1) % len(ms_9)]
                if tables_9[pi][(L, S, R)] != S:
                    priv.append(pi)
            if len(priv) == 1:
                movers.add(priv[0])
        print(f"  Component {i+1}: length={len(cyc)}, processors visited={sorted(movers)}")
    print()

    if not result_9.get('valid'):
        print("n=9 FAILED — skipping n=10.")
        return

    # === n=10 verification ===
    ms_10 = (2, 3, 3, 3, 3, 3, 3, 3, 3, 3)
    product_10 = 1
    for m in ms_10:
        product_10 *= m

    print(f"\n{'='*60}")
    print(f"Sol 3 v1 verification: n=10, ms={ms_10}, product={product_10}")
    print(f"{'='*60}\n")

    fs_10 = make_sol3v1_rules(ms_10)
    tables_10 = build_transition_tables(ms_10, fs_10)

    print("--- Verification with verifier.py (function-based) ---")
    result_10 = verify_system(list(ms_10), fs_10, verbose=True)
    print(f"  Valid: {result_10['valid']}")
    if result_10['valid']:
        print(f"  Cycle length: {result_10['cycle_length']}")
        for prop, (ok, info) in result_10['properties'].items():
            status = "PASS" if ok else "FAIL"
            print(f"  {prop}: {status} {info}")
        print(f"  Good configs: {len(result_10['good_configs'])}")
        print(f"  Bad configs: {product_10 - len(result_10['good_configs'])}")
    else:
        print(f"  Properties: {result_10['properties']}")
    print()

    print("--- Verification with docs/verify_witnesses.py (table-based) ---")
    ok_docs_10 = verify_with_docs_verifier("n=10, Sol3v1", ms_10, tables_10)
    print()

    print("--- Recurrent component analysis ---")
    num_comp_10, cycles_10 = count_recurrent_components(ms_10, tables_10)
    print(f"  Recurrent components: {num_comp_10}")
    for i, cyc in enumerate(cycles_10):
        movers = set()
        for cfg in cyc:
            priv = []
            for pi in range(len(ms_10)):
                L = cfg[(pi - 1) % len(ms_10)]
                S = cfg[pi]
                R = cfg[(pi + 1) % len(ms_10)]
                if tables_10[pi][(L, S, R)] != S:
                    priv.append(pi)
            if len(priv) == 1:
                movers.add(priv[0])
        print(f"  Component {i+1}: length={len(cyc)}, processors visited={sorted(movers)}")

    # Summary
    print(f"\n{'='*60}")
    print("SUMMARY")
    print(f"{'='*60}")
    print(f"n=9:  ms={ms_9}, product={product_9}, valid={result_9['valid']}", end="")
    if result_9['valid']:
        print(f", cycle_length={result_9['cycle_length']}, good_configs={len(result_9['good_configs'])}")
    else:
        print()
    print(f"n=10: ms={ms_10}, product={product_10}, valid={result_10['valid']}", end="")
    if result_10['valid']:
        print(f", cycle_length={result_10['cycle_length']}, good_configs={len(result_10['good_configs'])}")
    else:
        print()

    if result_9['valid'] and result_10['valid']:
        print(f"\nPattern M_n = 2·3^(n-1) CONFIRMED for n=9,10.")
        print(f"  n=9:  2·3^8 = {2*3**8}")
        print(f"  n=10: 2·3^9 = {2*3**9}")
    elif result_9['valid']:
        print(f"\nM_9 <= 13122 confirmed. Pattern breaks at n=10.")
    else:
        print(f"\nSol 3 v1 does NOT give a valid system at n=9.")


if __name__ == "__main__":
    main()
