#!/usr/bin/env python3
"""Final verification of cascade proof claims.

1. At n=8, adversary can ALWAYS avoid good configs via border fires.
2. The cycle from Step 1 in Part C actually exists.
3. Good cycle length bound at n=8.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import defaultdict, Counter
import random

from verifier import all_configs, privileged_set, apply_move, verify_system


def make_fs(tables):
    fs = []
    for table in tables:
        def make_f(t):
            def f(L, S, R): return t[(L, S, R)]
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


def adversary_avoidance_test(ms, tables, good_set, binary_state=(1,1,1)):
    """Test: can the adversary always avoid good configs via border fires?

    For each bad config c with given binary state where a border proc is privileged:
    check if ALL border-fire destinations are bad.
    If so: adversary successfully avoids good.
    If not: at least one destination is good -- adversary might be forced into it.
    """
    n = len(ms)
    fs = make_fs(tables)
    border = [3, n-1]

    bad_with_border_priv = []
    forced_to_good = 0
    can_stay_bad = 0

    for c in all_configs(ms):
        bt = (c[0], c[1], c[2])
        if bt != binary_state:
            continue
        if c in good_set:
            continue

        priv = privileged_set(c, fs, ms)
        border_priv = [p for p in priv if p in border]
        if not border_priv:
            continue

        # Check each border fire
        all_bad = True
        all_good = True
        for bp in border_priv:
            dest = apply_move(c, bp, fs, ms)
            if dest in good_set:
                all_bad = False
            else:
                all_good = False

        if all_bad:
            can_stay_bad += 1
        else:
            # Adversary has at least one border fire that goes to good.
            # But adversary WANTS to stay bad. If all border fires go to good,
            # adversary is forced to good (or can fire interior/binary instead).
            if all_good:
                forced_to_good += 1
            else:
                can_stay_bad += 1  # adversary picks the bad destination

    total = can_stay_bad + forced_to_good
    return can_stay_bad, forced_to_good, total


def verify_step1_cycle(ms, tables, good_set):
    """Verify Part C Step 1: adversary can create a bad cycle by staying at
    one binary state and alternating border + interior fires.

    Actually verify: the bad-config subgraph restricted to binary=(1,1,1)
    and non-binary moves has a cycle (or all paths drain to good).
    """
    n = len(ms)
    fs = make_fs(tables)

    # Bad configs at binary=(1,1,1)
    bad_111 = []
    for c in all_configs(ms):
        if (c[0], c[1], c[2]) != (1,1,1):
            continue
        if c not in good_set:
            bad_111.append(c)

    bad_111_set = set(bad_111)

    # Non-binary edges within bad_(1,1,1)
    succs = defaultdict(list)
    for c in bad_111:
        priv = privileged_set(c, fs, ms)
        non_bin_priv = [p for p in priv if p not in [0,1,2]]
        for p in non_bin_priv:
            dest = apply_move(c, p, fs, ms)
            if dest in bad_111_set:
                succs[c].append(dest)

    # Find SCCs in this subgraph
    sccs = tarjan_scc(bad_111, lambda v: succs.get(v, []))
    rec_sccs = [s for s in sccs if len(s) > 1 or
                (len(s) == 1 and next(iter(s)) in succs.get(next(iter(s)), []))]

    rec_total = sum(len(s) for s in rec_sccs)

    return len(bad_111), rec_total, len(rec_sccs)


def main():
    ms = (2, 2, 2, 3, 3, 3, 3, 4)
    n = len(ms)
    product = 1
    for m in ms:
        product *= m

    print(f"n={n}, ms={ms}, product={product}")

    # Build a system via good-targeting (mixed sweep)
    from ra_3cb_transition import (
        build_mixed_sweep_cycle, good_targeting_completion,
        cyclic_orders, make_fs_from_tables
    )

    # Find best system
    best_rec = float('inf')
    best_result = None
    non_binary = [p for p, m in enumerate(ms) if m > 2]
    target_ranges = [range(1, ms[p]) for p in non_binary]

    for combo in cartesian(*target_ranges):
        targets = {p: 1 for p, m in enumerate(ms) if m == 2}
        for idx, p in enumerate(non_binary):
            targets[p] = combo[idx]
        for order in cyclic_orders(n):
            for ret_same in (True, False):
                cycle = build_mixed_sweep_cycle(ms, order, targets, ret_same)
                if cycle is None:
                    continue
                comp = good_targeting_completion(ms, cycle)
                if comp is None:
                    continue
                tables = comp['tables']
                fs = comp['fs']
                good_set = set(cycle)
                break
            else:
                continue
            break
        else:
            continue
        break

    if tables is None:
        print("Failed to build system!")
        return

    good_set = set(cycle)
    print(f"Good cycle length: {len(good_set)}")

    # Test 1: Adversary avoidance
    print("\n" + "="*70)
    print("TEST 1: Adversary avoidance of good via border fires")
    print("="*70)

    for bt in [(0,0,0), (1,1,1), (0,1,0), (1,0,1)]:
        can_bad, forced_good, total = adversary_avoidance_test(ms, tables, good_set, bt)
        print(f"  Binary {bt}: {total} bad with border priv, "
              f"{can_bad} can stay bad ({can_bad/max(1,total):.1%}), "
              f"{forced_good} forced to good ({forced_good/max(1,total):.1%})")

    # Test 2: Non-binary bad cycle at binary=(1,1,1)
    print("\n" + "="*70)
    print("TEST 2: Non-binary bad cycle at fixed binary state")
    print("="*70)

    for bt_idx, bt in enumerate(cartesian([0,1], [0,1], [0,1])):
        bt = tuple(bt)
        n_bad, n_rec, n_sccs = verify_step1_cycle(ms, tables, good_set)
        if bt_idx == 0:
            print(f"  Binary (1,1,1): {n_bad} bad, {n_rec} in {n_sccs} rec SCCs")
            break

    # Test 3: Full bad-config graph cycle analysis
    print("\n" + "="*70)
    print("TEST 3: Full bad-config graph analysis")
    print("="*70)

    fs = make_fs(tables)
    configs = list(all_configs(ms))
    bad = [c for c in configs if c not in good_set]
    bad_set = set(bad)

    bad_succs = defaultdict(list)
    for c in bad:
        priv = privileged_set(c, fs, ms)
        for p in priv:
            dest = apply_move(c, p, fs, ms)
            if dest in bad_set:
                bad_succs[c].append(dest)

    sccs = tarjan_scc(bad, lambda v: bad_succs.get(v, []))
    rec = [s for s in sccs if len(s) > 1 or
           (len(s) == 1 and next(iter(s)) in bad_succs.get(next(iter(s)), []))]
    rec_total = sum(len(s) for s in rec)

    print(f"  Total bad: {len(bad)}")
    print(f"  Recurrent bad: {rec_total}")
    print(f"  Number of rec SCCs: {len(rec)}")
    sizes = Counter(len(s) for s in rec)
    print(f"  SCC size distribution: {dict(sorted(sizes.items(), reverse=True))}")

    # Analyze the large SCCs
    for scc in sorted(rec, key=len, reverse=True)[:3]:
        if len(scc) < 10:
            break
        # Check which binary triples appear
        bt_count = Counter()
        for c in scc:
            bt_count[(c[0], c[1], c[2])] += 1
        print(f"\n  SCC of size {len(scc)}:")
        print(f"    Binary triples: {dict(sorted(bt_count.items()))}")

        # Check which procs fire in this SCC
        procs_active = set()
        for c in scc:
            for dest in bad_succs.get(c, []):
                if dest in scc:
                    for p in range(n):
                        if c[p] != dest[p]:
                            procs_active.add(p)
        print(f"    Active procs: {sorted(procs_active)}")

    # Test 4: Good cycle length analysis
    print("\n" + "="*70)
    print("TEST 4: Good cycle statistics")
    print("="*70)

    # How many good configs at each binary triple?
    bt_good = Counter()
    for c in good_set:
        bt_good[(c[0], c[1], c[2])] += 1

    print("  Good per binary triple:")
    for bt in sorted(bt_good.keys()):
        nb_total = product // 8
        print(f"    {bt}: {bt_good[bt]} / {nb_total} = {bt_good[bt]/nb_total:.1%}")

    # P1 fire analysis
    print("\n  P1 mover analysis:")
    p1_mover_contexts = set()
    for c in good_set:
        priv = privileged_set(c, fs, ms)
        if len(priv) == 1 and priv[0] == 1:
            ctx = (c[0], c[1], c[2])
            p1_mover_contexts.add(ctx)
            print(f"    P1 fires at ctx={ctx}, config=...{c[3:]}")

    print(f"  P1 mover contexts: {p1_mover_contexts}")
    print(f"  P1 fires {len(p1_mover_contexts)} times")


if __name__ == '__main__':
    main()
