#!/usr/bin/env python3
"""Investigate cascade cycle unavoidability for 3CB at n>=8.

Key questions:
1. For each P1 mover choice, what is the binary firing pattern in cascade cycles?
2. Is border privilege forced by liveness after binary state changes?
3. What is the minimum cascade cycle length for each P1 mover?
4. How many table entries does a cascade cycle constrain?
5. Why does this become unavoidable at n>=8?
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import defaultdict, Counter
import time

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


def build_tables_for_mover(ms, p1_s0_mover, good_cycle):
    """Build transition tables compatible with given P1 mover and good cycle."""
    n = len(ms)
    tables = [dict() for _ in range(n)]

    # Fill from good cycle
    for i in range(len(good_cycle)):
        c = good_cycle[i]
        c_next = good_cycle[(i+1) % len(good_cycle)]
        # Find which proc fires
        for p in range(n):
            if c[p] != c_next[p]:
                L = c[(p-1) % n]
                S = c[p]
                R = c[(p+1) % n]
                tables[p][(L, S, R)] = c_next[p]
                break

    # Set P1 mover contexts
    a, _, cc = p1_s0_mover
    p1_s1_mover = (1-a, 1, 1-cc)

    # P1 fires at p1_s0_mover and p1_s1_mover
    tables[1][p1_s0_mover] = 1  # 0 -> 1
    tables[1][p1_s1_mover] = 0  # 1 -> 0

    # P1 stays at all other contexts
    for L in range(ms[0]):
        for R in range(ms[2]):
            for S in range(ms[1]):
                ctx = (L, S, R)
                if ctx not in tables[1]:
                    tables[1][ctx] = S  # stay

    # Complete remaining tables: non-mover contexts -> stay
    for p in range(n):
        if p == 1:
            continue
        for L in range(ms[(p-1) % n]):
            for S in range(ms[p]):
                for R in range(ms[(p+1) % n]):
                    ctx = (L, S, R)
                    if ctx not in tables[p]:
                        tables[p][ctx] = S  # default: stay (no privilege)

    return tables


def analyze_bad_graph(ms, fs, good_set):
    """Analyze bad-config graph structure."""
    n = len(ms)
    configs = list(all_configs(ms))
    bad = [c for c in configs if c not in good_set]
    bad_set = set(bad)

    bad_succs = defaultdict(list)
    for c in bad:
        priv = privileged_set(c, fs, ms)
        for i in priv:
            s = apply_move(c, i, fs, ms)
            if s in bad_set:
                bad_succs[c].append((s, i))

    # Count dead configs (no privilege at all)
    all_priv = {}
    dead = 0
    for c in configs:
        p = privileged_set(c, fs, ms)
        all_priv[c] = p
        if not p:
            dead += 1

    sccs = tarjan_scc(bad, lambda v: [s for s, _ in bad_succs.get(v, [])])
    recurrent = [s for s in sccs if len(s) > 1 or
                 (len(s) == 1 and any(s2 == next(iter(s)) for s2, _ in bad_succs.get(next(iter(s)), [])))]

    rec_total = sum(len(s) for s in recurrent)
    return {
        'bad': len(bad),
        'dead': dead,
        'recurrent': rec_total,
        'sccs': recurrent,
        'bad_succs': bad_succs,
        'priv_map': all_priv,
    }


def liveness_analysis(ms):
    """For each binary state triple, count how many non-binary extensions
    have NO privileged proc among the non-binary procs.
    These configs MUST have a binary proc privileged for liveness."""
    n = len(ms)
    non_binary = [p for p in range(n) if ms[p] > 2]
    binary = [p for p in range(n) if ms[p] == 2]

    non_binary_ranges = [range(ms[p]) for p in non_binary]

    print(f"\nLiveness analysis: n={n}, ms={ms}")
    print(f"Binary procs: {binary}, Non-binary procs: {non_binary}")
    print(f"Non-binary state space: {' x '.join(str(ms[p]) for p in non_binary)} = ", end='')
    nb_total = 1
    for p in non_binary:
        nb_total *= ms[p]
    print(nb_total)

    # For each binary triple, we need at least one proc to be privileged.
    # If NO non-binary proc is privileged, then a binary proc MUST be.
    # This constrains the binary transition tables.

    for bvals in cartesian(*[range(2) for _ in binary]):
        print(f"\n  Binary state {bvals}:")
        # How many non-binary extensions exist?
        total_ext = nb_total
        print(f"    Total extensions: {total_ext}")


def border_privilege_after_sweep(ms, tables, direction='up'):
    """After binary sweep, check which configs have border procs privileged."""
    n = len(ms)

    if direction == 'up':
        # After sweep: binary = (1,1,1)
        bin_state = (1, 1, 1)
    else:
        bin_state = (0, 0, 0)

    border_procs = [3, n-1]

    # For each non-binary state, check if any border proc is privileged
    non_binary = [p for p in range(n) if ms[p] > 2]
    non_binary_ranges = [range(ms[p]) for p in non_binary]

    border_priv_count = 0
    no_border_priv = 0
    total = 0

    fs = []
    for table in tables:
        def make_f(t):
            def f(L, S, R):
                return t[(L, S, R)]
            return f
        fs.append(make_f(table))

    for nb_vals in cartesian(*non_binary_ranges):
        config = [0] * n
        for i, b in enumerate([0, 1, 2]):
            config[b] = bin_state[i]
        for i, p in enumerate(non_binary):
            config[p] = nb_vals[i]
        config = tuple(config)

        total += 1
        has_border = False
        for bp in border_procs:
            L = config[(bp-1) % n]
            S = config[bp]
            R = config[(bp+1) % n]
            if tables[bp][(L, S, R)] != S:
                has_border = True
                break

        if has_border:
            border_priv_count += 1
        else:
            no_border_priv += 1

    return border_priv_count, no_border_priv, total


def count_constrained_entries(ms, good_cycle):
    """Count how many transition table entries are constrained by the good cycle."""
    n = len(ms)
    constrained = defaultdict(set)  # proc -> set of constrained (L,S,R) contexts

    for i in range(len(good_cycle)):
        c = good_cycle[i]
        c_next = good_cycle[(i+1) % len(good_cycle)]

        # Find mover
        mover = None
        for p in range(n):
            if c[p] != c_next[p]:
                mover = p
                break

        if mover is not None:
            # Mover entry constrained
            L = c[(mover-1) % n]
            S = c[mover]
            R = c[(mover+1) % n]
            constrained[mover].add((L, S, R))

        # Non-mover entries: each non-mover proc must stay
        for p in range(n):
            if p != mover:
                L = c[(p-1) % n]
                S = c[p]
                R = c[(p+1) % n]
                constrained[p].add((L, S, R))

    return constrained


def main():
    # Test at n=8
    ms = (2, 2, 2, 3, 3, 3, 3, 4)
    n = len(ms)
    product = 1
    for m in ms:
        product *= m

    print(f"n={n}, ms={ms}, product={product}")
    print(f"Configs per binary context: {product // 8}")

    # For each of the 4 P1 mover choices, build a system and analyze
    movers_s0 = [(0,0,0), (0,0,1), (1,0,0), (1,0,1)]

    # First, build a simple good cycle (mixed sweep, CW)
    order = list(range(n))
    targets = {p: 1 for p in range(n)}

    # Simple sweep cycle: all-0 -> fire each proc CW -> all-targets -> fire each proc CW back
    cycle = []
    config = tuple([0] * n)
    cycle.append(config)
    for p in order:
        config = list(cycle[-1])
        config[p] = 1 if ms[p] == 2 else targets[p]
        cycle.append(tuple(config))
    for p in order:
        config = list(cycle[-1])
        config[p] = 0
        cycle.append(tuple(config))
    # Remove last (duplicate of first)
    if cycle[-1] == cycle[0]:
        cycle = cycle[:-1]

    good_set = set(cycle)
    print(f"\nGood cycle length: {len(cycle)}")

    # Count constrained entries
    constrained = count_constrained_entries(ms, cycle)
    total_contexts = sum(ms[(p-1)%n] * ms[p] * ms[(p+1)%n] for p in range(n))
    total_constrained = sum(len(v) for v in constrained.values())
    print(f"Total constrained contexts: {total_constrained} / {total_contexts}")
    for p in range(n):
        ctx_size = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
        print(f"  P{p}: {len(constrained[p])} / {ctx_size} contexts constrained")

    # Now analyze liveness constraint
    print("\n" + "="*70)
    print("LIVENESS CONSTRAINT ANALYSIS")
    print("="*70)

    # Key question: after binary sweep to (1,1,1), how many configs have
    # NO privileged non-binary proc?
    # If such configs exist, a binary proc must be privileged -> but binary procs
    # are all at state 1, so f(L,1,R)!=1 means they fire back to 0.

    # For the border proc P3: ctx = (c2, c3, c4).
    # After sweep UP: c2 = 1. So ctx = (1, c3, c4).
    # P3 is privileged iff f3(1, c3, c4) != c3.
    # Total (c3, c4) pairs: 3 * 3 = 9.
    # P3's table at (1, *, *): 9 entries. Each is either c3 (stay) or something else (fire).
    # Good cycle constrains some of these.

    # For the border proc P7: ctx = (c6, c7, c0).
    # After sweep UP: c0 = 1. So ctx = (c6, c7, 1).
    # ms[7] = 4, so 3 * 4 = 12 contexts at R=1.

    print("\nBorder proc context analysis after binary sweep UP (binary=(1,1,1)):")
    print(f"  P3: ctx = (1, c3, c4), c3 in {{0,1,2}}, c4 in {{0,1,2}} -> 9 contexts")
    print(f"  P7: ctx = (c6, c7, 1), c6 in {{0,1,2}}, c7 in {{0,1,2,3}} -> 12 contexts")

    # For liveness: every config must have at least one privileged proc.
    # Consider config (1,1,1, c3, c4, c5, c6, c7) [all binary=1].
    # Privileged binary procs:
    #   P0: f0(c7, 1, 1) != 1
    #   P1: f1(1, 1, c2=1) = f1(1,1,1) != 1. Only if (1,1,1) is P1's S=1 mover.
    #   P2: f2(1, 1, c3) != 1

    print("\n" + "="*70)
    print("FIBER COUPLING ANALYSIS")
    print("="*70)

    # P1 fires at (L,S,R) -> ALL configs with that (L,S,R) at P1 fire the same way.
    # With product/8 = 324 configs per binary triple, P1's firing at one context
    # moves 324 configs simultaneously.

    # Good cycle has ~16 configs. Each binary triple appears at most 16/8 = 2 times.
    # So of 324 configs with binary=(0,0,0), at most 2 are good.
    # The other 322 are bad. ALL 322 fire identically when P1 fires.

    print(f"Configs per binary triple: {product // 8}")
    print(f"Good configs: ~{len(cycle)}")
    print(f"Good per binary triple: ~{len(cycle) / 8:.1f}")
    print(f"Bad per binary triple: ~{product // 8 - len(cycle) / 8:.1f}")

    # Count good configs per binary triple
    bin_good = Counter()
    for c in cycle:
        bin_good[(c[0], c[1], c[2])] += 1
    print("\nGood configs per binary triple:")
    for bt in sorted(bin_good.keys()):
        print(f"  {bt}: {bin_good[bt]}")

    print("\n" + "="*70)
    print("INTERIOR DAG + BOUNDARY COUNTING")
    print("="*70)

    # Interior procs: {4,5,6} at n=8, states 3*3*3=27
    # With border proc 7 having 4 states, border states: 3*4=12
    # Total non-binary configs: 12 * 27 = 324

    # The interior is a DAG under each fixed boundary (c3, c7).
    # Boundary conditions: c3 in {0,1,2}, c7 in {0,1,2,3} -> 12 values.
    # But border PROCS are just P3 and P7.
    # The "boundary" in the cascade is (c3, c7) restricted to binary-adjacent values.

    # For n=7: interior = {4,5}, states 3*3=9
    # For n=8: interior = {4,5,6}, states 3*3*3=27 (or 3*3*4=36 with P7's 4 states)

    # Actually at n=8 with ms=(2,2,2,3,3,3,3,4):
    # Interior: P4(3), P5(3), P6(3)
    # Borders: P3(3), P7(4)
    # Non-binary state space: 3*3*3*3*4 = 324

    # At n=7 with ms=(2,2,2,3,3,3,4):
    # Interior: P4(3), P5(3)
    # Borders: P3(3), P6(4)
    # Non-binary state space: 3*3*3*4 = 108

    print("n=7: interior {4,5}, 9 states. Borders {3,6}. Total non-binary: 108")
    print("n=8: interior {4,5,6}, 27 states. Borders {3,7}. Total non-binary: 324")

    # Cascade cycle constrains 16 table entries.
    # At n=8, total table entries = sum of context sizes per proc.
    # Total free entries after good cycle = total_contexts - total_constrained.

    total_entries = sum(ms[(p-1)%n] * ms[p] * ms[(p+1)%n] for p in range(n))
    print(f"\nTotal table entries: {total_entries}")
    print(f"Constrained by good cycle: {total_constrained}")
    print(f"Free entries: {total_entries - total_constrained}")

    # The cascade cycle uses 16 free entries.
    # If 16 << free entries, the cascade CAN be blocked by choosing those entries.
    # If the cascade's 16 entries are FORCED (by other constraints), it CANNOT be blocked.

    print(f"\nCascade uses 16 entries. Free: {total_entries - total_constrained}.")
    print(f"Ratio: {16 / (total_entries - total_constrained):.4f}")

    print("\n" + "="*70)
    print("N-SCALING OF KEY RATIOS")
    print("="*70)

    for nn in range(5, 12):
        # 3CB: first 3 procs binary, rest ternary except last which is 4
        # (to keep sub-threshold)
        if nn == 5:
            mms = (2,2,2,3,4)
        elif nn == 6:
            mms = (2,2,2,3,3,4)
        elif nn == 7:
            mms = (2,2,2,3,3,3,4)
        elif nn == 8:
            mms = (2,2,2,3,3,3,3,4)
        else:
            mms = tuple([2,2,2] + [3]*(nn-4) + [4])

        prod = 1
        for m in mms:
            prod *= m
        threshold = 4 * (3 ** (nn-2))

        non_bin = prod // 8
        # Good cycle length for mixed sweep: 2*n
        gc_len = 2 * nn
        # Interior procs: nn - 5 (binary 3 + border 2)
        n_interior = nn - 5
        interior_states = 3 ** n_interior if n_interior > 0 else 1
        # Interior states with border: 3 * 4 * 3^(n_interior) = 12 * 3^(n_interior)
        # Actually border states depend on ms

        # Configs per binary triple
        cpbt = non_bin
        # Bad per binary triple (good cycle: ~2 per triple)
        bad_pbt = cpbt - 2  # approximate

        # Bottleneck ratio
        ratio = bad_pbt / gc_len if gc_len > 0 else 0

        print(f"n={nn}: ms={mms}, prod={prod}, thresh={threshold}, sub={prod<threshold}")
        print(f"  non-binary configs: {non_bin}, interior states: {interior_states}")
        print(f"  bad per binary triple: ~{bad_pbt}, good cycle: ~{gc_len}")
        print(f"  bottleneck ratio: {ratio:.1f}")
        print()


if __name__ == '__main__':
    main()
