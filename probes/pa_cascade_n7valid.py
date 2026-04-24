#!/usr/bin/env python3
"""Check if the known valid n=7 system has cascade cycles.

The answer must be NO (valid system = no bad cycles).
But what does the adversary simulation do? It should reach good configs.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from verifier import all_configs, privileged_set, apply_move, verify_system
from cycle_first_search import witness_n7
from collections import defaultdict, Counter


def make_fs(tables):
    fs = []
    for table in tables:
        def make_f(t):
            def f(L, S, R):
                return t[(L, S, R)]
            return f
        fs.append(make_f(table))
    return fs


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


def main():
    # Get n=7 valid witness
    ms7, tables7 = witness_n7()
    n = len(ms7)
    print(f"n={n}, ms={ms7}")

    product = 1
    for m in ms7:
        product *= m
    print(f"product={product}")

    # Verify it's valid
    fs = make_fs(tables7)
    result = verify_system(list(ms7), fs, verbose=False)
    print(f"Valid: {result['valid']}")

    if not result['valid']:
        print(f"Properties: {result.get('properties', {})}")
        return

    good_set = result.get('good_configs', set())
    print(f"Good configs: {len(good_set)}")

    # Check privilege structure at binary=(1,1,1)
    binary_procs = [p for p in range(n) if ms7[p] == 2]
    print(f"Binary procs: {binary_procs}")

    # Count configs at binary=(1,1,1)
    bin_111_configs = []
    for c in all_configs(ms7):
        if all(c[p] == 1 for p in binary_procs):
            bin_111_configs.append(c)

    print(f"Configs at binary=(1,1,1): {len(bin_111_configs)}")

    good_111 = [c for c in bin_111_configs if c in good_set]
    bad_111 = [c for c in bin_111_configs if c not in good_set]
    print(f"Good at (1,1,1): {len(good_111)}")
    print(f"Bad at (1,1,1): {len(bad_111)}")

    # For each bad config at (1,1,1), what procs are privileged?
    border = [binary_procs[-1] + 1, (binary_procs[0] - 1) % n]
    # Actually, border procs depend on where binary procs are
    # Binary at positions binary_procs. The border procs are those adjacent to binary.
    # For 3CB at positions 0,1,2: border procs are 3 and n-1.
    border = [3, n-1]
    interior = [p for p in range(4, n-1)]

    print(f"Border: {border}, Interior: {interior}")

    priv_stats = Counter()
    for c in bad_111:
        priv = privileged_set(c, fs, ms7)
        has_border = any(p in border for p in priv)
        has_binary = any(p in binary_procs for p in priv)
        has_interior = any(p in interior for p in priv)
        key = (has_binary, has_border, has_interior)
        priv_stats[key] += 1

    print(f"\nPrivilege types at bad binary=(1,1,1):")
    for key, count in sorted(priv_stats.items()):
        has_bin, has_brd, has_int = key
        label = []
        if has_bin: label.append('bin')
        if has_brd: label.append('brd')
        if has_int: label.append('int')
        print(f"  {'+'.join(label) if label else 'dead'}: {count}")

    # Check: how does the valid system drain bad configs at binary=(1,1,1)?
    # Follow paths from bad configs
    bad_set = set(c for c in all_configs(ms7) if c not in good_set)

    print(f"\nDrainage analysis from binary=(1,1,1):")
    max_depth = 0
    path_lengths = []

    for c in bad_111[:50]:  # Sample 50
        depth = 0
        current = c
        visited = set()
        while current in bad_set and depth < 200:
            visited.add(current)
            priv = privileged_set(current, fs, ms7)
            if not priv:
                depth = -1
                break
            # Follow first privileged proc
            next_c = apply_move(current, priv[0], fs, ms7)
            if next_c in visited:
                depth = -2  # cycle (shouldn't happen in valid system)
                break
            current = next_c
            depth += 1

        if depth >= 0:
            path_lengths.append(depth)
            max_depth = max(max_depth, depth)
        else:
            print(f"  Config {c}: depth={depth}")

    if path_lengths:
        print(f"  Path lengths (sample 50): min={min(path_lengths)}, max={max(path_lengths)}, "
              f"mean={sum(path_lengths)/len(path_lengths):.1f}")

    # Now check: what is the valid n=7 system's ms orientation?
    # The key question: are the binary procs at positions 0,1,2?
    print(f"\nState vector: {ms7}")
    print(f"Binary positions: {[p for p in range(n) if ms7[p] == 2]}")

    # Check the good cycle structure
    if good_set:
        # Which binary triples appear in the good cycle?
        bin_triples = Counter()
        for c in good_set:
            bt = tuple(c[p] for p in binary_procs)
            bin_triples[bt] += 1
        print(f"\nGood cycle binary triples:")
        for bt, count in sorted(bin_triples.items()):
            print(f"  {bt}: {count}")


if __name__ == '__main__':
    main()
