#!/usr/bin/env python3
"""Detail on adversary avoidance: can the adversary ALWAYS find a starting
config where border fire stays bad?

The test showed 214/232 can stay bad at (1,1,1). But 18 are forced to good.
Question: can the adversary reach the 214 "safe" configs from any starting config?

Actually, the adversary doesn't need border-fire avoidance. The key insight
from Test 2 is that there are already bad cycles WITHIN the non-binary subgraph
at binary=(1,1,1). The adversary just needs to reach one of these cycles.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import defaultdict, Counter

from verifier import all_configs, privileged_set, apply_move
from ra_3cb_transition import (
    build_mixed_sweep_cycle, good_targeting_completion,
    cyclic_orders, make_fs_from_tables
)


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


def main():
    ms = (2, 2, 2, 3, 3, 3, 3, 4)
    n = len(ms)

    # Build system
    non_binary = [p for p, m in enumerate(ms) if m > 2]
    for combo in cartesian(*[range(1, ms[p]) for p in non_binary]):
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
                good_set = set(cycle)
                break
            else:
                continue
            break
        else:
            continue
        break

    fs = make_fs(tables)
    print(f"n={n}, ms={ms}, good cycle={len(good_set)}")

    # Analyze full bad graph
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

    # Recurrent SCCs
    sccs = tarjan_scc(bad, lambda v: bad_succs.get(v, []))
    rec = [s for s in sccs if len(s) > 1 or
           (len(s) == 1 and next(iter(s)) in bad_succs.get(next(iter(s)), []))]

    rec_set = set()
    for s in rec:
        rec_set |= s

    print(f"Total bad: {len(bad)}")
    print(f"Recurrent bad: {len(rec_set)}")
    print(f"Number of rec SCCs: {len(rec)}")

    # For each rec SCC: analyze its binary triple distribution and proc usage
    print("\nRecurrent SCC analysis:")
    for i, scc in enumerate(sorted(rec, key=len, reverse=True)):
        bt_count = Counter()
        procs_used = set()
        for c in scc:
            bt_count[(c[0], c[1], c[2])] += 1
        for c in scc:
            for dest in bad_succs.get(c, []):
                if dest in scc:
                    for p in range(n):
                        if c[p] != dest[p]:
                            procs_used.add(p)

        n_bt = len(bt_count)
        has_binary = any(p in [0,1,2] for p in procs_used)
        print(f"  SCC {i}: size={len(scc)}, binary triples={n_bt}, "
              f"procs={sorted(procs_used)}, has_binary_fire={has_binary}")

    # Key question: are there rec SCCs WITHOUT binary fires?
    # These would be purely border+interior cycles.
    print("\n" + "="*70)
    print("SCCs without binary fires (pure border+interior cycles):")
    print("="*70)

    for i, scc in enumerate(sorted(rec, key=len, reverse=True)):
        procs_used = set()
        for c in scc:
            for dest in bad_succs.get(c, []):
                if dest in scc:
                    for p in range(n):
                        if c[p] != dest[p]:
                            procs_used.add(p)

        has_binary = any(p in [0,1,2] for p in procs_used)
        if not has_binary:
            bt_count = Counter()
            for c in scc:
                bt_count[(c[0], c[1], c[2])] += 1
            print(f"  SCC {i}: size={len(scc)}, binary triples={dict(bt_count)}")
            print(f"    Procs: {sorted(procs_used)}")

            # Show a sample cycle
            start = min(scc)
            path = [start]
            current = start
            for _ in range(20):
                dests = [d for d in bad_succs.get(current, []) if d in scc]
                if not dests:
                    break
                nxt = dests[0]
                if nxt == start and len(path) > 1:
                    break
                path.append(nxt)
                current = nxt

            if current == start or (len(path) > 1 and path[-1] in [d for d in bad_succs.get(path[-2], []) if d in scc]):
                print(f"    Sample cycle length: {len(path)}")
                for j, c in enumerate(path[:min(8, len(path))]):
                    priv = privileged_set(c, fs, ms)
                    p_types = []
                    for p in priv:
                        if p in [0,1,2]: p_types.append(f'B{p}')
                        elif p in [3, n-1]: p_types.append(f'R{p}')
                        else: p_types.append(f'I{p}')
                    print(f"      [{j}] {c} priv={p_types}")

    # Reachability: can every bad config reach some rec SCC?
    print("\n" + "="*70)
    print("Reachability: can every bad config reach a rec SCC?")
    print("="*70)

    # BFS from each bad config to check if it can reach rec_set
    can_reach_rec = 0
    stuck_not_rec = 0

    for c in bad:
        if c in rec_set:
            can_reach_rec += 1
            continue

        # BFS
        visited = {c}
        queue = [c]
        found = False
        while queue:
            node = queue.pop(0)
            for dest in bad_succs.get(node, []):
                if dest in rec_set:
                    found = True
                    break
                if dest not in visited:
                    visited.add(dest)
                    queue.append(dest)
            if found:
                break

        if found:
            can_reach_rec += 1
        else:
            stuck_not_rec += 1

    print(f"  Bad configs that can reach rec SCC: {can_reach_rec}")
    print(f"  Bad configs stuck (no path to rec): {stuck_not_rec}")
    print(f"  (Stuck configs drain to good)")


if __name__ == '__main__':
    main()
