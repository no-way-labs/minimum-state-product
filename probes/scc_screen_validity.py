#!/usr/bin/env python3
"""scc_screen_validity.py — Is the SCC screen sound?

Critical question: The SCC screen rejects Dijkstra's Solution 3 (which works).
This means the screen produces false positives.

Test: Build the COMPLETE transition graph for Dijkstra's Sol 3 and verify
no non-legitimate configs are trapped. Then compare with the screen's result.
"""

from itertools import product as cartesian
from collections import Counter


def dijkstra_sol3_rule(i, L, S, R, n, K=3):
    """Dijkstra's Solution 3 complete rule.
    Returns the new value for processor i, given (L, S, R).
    If i is not privileged, returns S (no change).
    """
    if i == 0:
        target = (L + 1) % K  # L is actually s_{n-1} for P_0, but in ring, left neighbor
        # Wait — in the ring, P_0's left neighbor is P_{n-1}.
        # P_0 is privileged if s_0 ≠ (s_{n-1} + 1) mod K.
        # L = s_{(0-1) mod n} = s_{n-1}.
        target = (L + 1) % K
        if S != target:
            return target  # privileged, move
        else:
            return S  # not privileged
    else:
        # P_i (i>0): privileged if s_i ≠ s_{i-1}. Move: s_i := s_{i-1}.
        if S != L:
            return L
        else:
            return S


def find_sccs(forced_succs):
    """Iterative Tarjan SCC."""
    index_counter = [0]
    stack = []
    on_stack = set()
    index_map = {}
    lowlink = {}
    sccs = []

    def strongconnect_iter(v):
        work = [(v, 0)]
        index_map[v] = lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        while work:
            node, si = work[-1]
            succs = forced_succs.get(node, [])
            if si < len(succs):
                work[-1] = (node, si + 1)
                w = succs[si]
                if w not in index_map:
                    index_map[w] = lowlink[w] = index_counter[0]
                    index_counter[0] += 1
                    stack.append(w)
                    on_stack.add(w)
                    work.append((w, 0))
                elif w in on_stack:
                    lowlink[node] = min(lowlink[node], index_map[w])
            else:
                if lowlink[node] == index_map[node]:
                    scc = []
                    while True:
                        w = stack.pop()
                        on_stack.discard(w)
                        scc.append(w)
                        if w == node:
                            break
                    if len(scc) > 1 or (len(scc) == 1 and node in forced_succs.get(node, [])):
                        sccs.append(scc)
                work.pop()
                if work:
                    parent = work[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[node])

    for v in forced_succs:
        if v not in index_map:
            strongconnect_iter(v)

    return sccs


def main():
    n = 9
    K = 3
    print("=" * 70)
    print("SCC SCREEN VALIDITY CHECK")
    print("=" * 70)

    # Build Dijkstra's complete rule table
    all_configs = list(cartesian(*(range(K) for _ in range(n))))
    complete_rule = {}
    for i in range(n):
        for L in range(K):
            for S in range(K):
                for R in range(K):
                    complete_rule[(i, L, S, R)] = dijkstra_sol3_rule(i, L, S, R, n, K)

    # Find legitimate configs (exactly 1 privilege)
    legitimate = []
    for c in all_configs:
        privs = []
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            if complete_rule[(i, L, S, R)] != S:
                privs.append(i)
        if len(privs) == 1:
            legitimate.append(c)

    legitimate_set = set(legitimate)
    non_legit = [c for c in all_configs if c not in legitimate_set]
    print(f"\n  Total configs: {len(all_configs)}")
    print(f"  Legitimate: {len(legitimate)}")
    print(f"  Non-legitimate: {len(non_legit)}")

    # Build complete forced-successor graph on NON-legitimate configs
    # Every privileged processor at a non-legit config gives a transition
    # If any of those transitions lead to another non-legit config, it's a forced edge
    print(f"\n--- Complete forced-successor graph (non-legit → non-legit) ---")

    forced_succs_complete = {}
    for c in non_legit:
        succs = []
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            new_val = complete_rule[(i, L, S, R)]
            if new_val != S:
                new_c = list(c)
                new_c[i] = new_val
                new_c = tuple(new_c)
                if new_c in set(non_legit):
                    succs.append(new_c)
        if succs:
            forced_succs_complete[c] = succs

    sccs_complete = find_sccs(forced_succs_complete)
    sizes = sorted([len(s) for s in sccs_complete], reverse=True)
    print(f"  SCCs in COMPLETE graph: {len(sccs_complete)}, sizes={sizes}, total={sum(sizes)}")

    # Now check: every non-legit config should have at least one successor
    # that leads toward a legit config (not back to non-legit)
    n_escape = 0
    n_trapped = 0
    for c in non_legit:
        has_legit_succ = False
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            new_val = complete_rule[(i, L, S, R)]
            if new_val != S:
                new_c = list(c)
                new_c[i] = new_val
                new_c = tuple(new_c)
                if tuple(new_c) in legitimate_set:
                    has_legit_succ = True
                    break
        if has_legit_succ:
            n_escape += 1
        else:
            n_trapped += 1

    print(f"\n  Non-legit configs with direct legit successor: {n_escape}")
    print(f"  Non-legit configs with NO direct legit successor: {n_trapped}")
    print(f"  (Trapped configs must reach legit via multi-step path)")

    # Now the key comparison: build the PARTIAL forced graph (good-cycle only)
    # and show it has SCCs while the complete graph does not
    print(f"\n--- Partial forced graph (good-cycle-determined entries only) ---")

    # Build good cycle
    start = (0,) * n
    cycle = [start]
    c = start
    seen_cyc = {start}
    while True:
        privs = []
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            if complete_rule[(i, L, S, R)] != S:
                privs.append(i)
        assert len(privs) == 1, f"Non-unique privilege in legit config: {c} has {privs}"
        mover = privs[0]
        new_c = list(c)
        new_c[mover] = complete_rule[(mover, c[(mover-1)%n], c[mover], c[(mover+1)%n])]
        new_c = tuple(new_c)
        if new_c in seen_cyc:
            break
        cycle.append(new_c)
        seen_cyc.add(new_c)
        c = new_c

    print(f"  Good cycle length: {len(cycle)}")

    # Extract determined entries from good cycle
    det = {}
    for idx in range(len(cycle)):
        c_cur = cycle[idx]
        c_nxt = cycle[(idx + 1) % len(cycle)]
        diffs = [j for j in range(n) if c_cur[j] != c_nxt[j]]
        mover = diffs[0]
        for i in range(n):
            L = c_cur[(i-1) % n]; S = c_cur[i]; R = c_cur[(i+1) % n]
            if i == mover:
                det[(i, L, S, R)] = c_nxt[i]
            else:
                det[(i, L, S, R)] = S

    good_set = set(cycle)
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    # Build partial forced graph
    forced_succs_partial = {}
    for c in non_good:
        succs = []
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            key = (i, L, S, R)
            if key in det and det[key] != S:
                new_c = list(c)
                new_c[i] = det[key]
                new_c = tuple(new_c)
                if new_c in non_good_set:
                    succs.append(new_c)
        if succs:
            forced_succs_partial[c] = succs

    sccs_partial = find_sccs(forced_succs_partial)
    sizes_partial = sorted([len(s) for s in sccs_partial], reverse=True)
    print(f"  SCCs in PARTIAL graph: {len(sccs_partial)}, sizes={sizes_partial}, total={sum(sizes_partial)}")

    # Compare
    print(f"\n{'=' * 70}")
    print(f"COMPARISON")
    print(f"{'=' * 70}")
    print(f"  Complete Dijkstra graph: {len(sccs_complete)} SCCs, total {sum(s for s in [len(sc) for sc in sccs_complete])} configs")
    print(f"  Partial (good-cycle) graph: {len(sccs_partial)} SCCs, total {sum(sizes_partial)} configs")
    print()

    if len(sccs_complete) == 0 and len(sccs_partial) > 0:
        print("  *** CONFIRMED: SCC screen produces FALSE POSITIVES! ***")
        print("  The complete graph has no SCCs, but the partial graph does.")
        print("  This means the screen incorrectly rejects viable cycles.")
        print()
        print("  IMPLICATIONS:")
        print("  1. All 'DEAD' classifications from Explorations 1-3 may be invalid")
        print("  2. The SCC screen cannot be used as a proof of infeasibility")
        print("  3. Cycles rejected by the screen may still be completable")
        print("  4. The binary search for 'where SCCs break' is asking the wrong question")
    elif len(sccs_complete) > 0:
        print("  Complete graph ALSO has SCCs — need different analysis")
        # Check if every SCC config has an escape via ANY move
        for si, scc in enumerate(sccs_complete):
            scc_set = set(scc)
            n_with_escape = 0
            for c in scc:
                has_escape = False
                for i in range(n):
                    L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
                    new_val = complete_rule[(i, L, S, R)]
                    if new_val != S:
                        new_c = list(c)
                        new_c[i] = new_val
                        new_c = tuple(new_c)
                        if tuple(new_c) not in scc_set:
                            has_escape = True
                            break
                if has_escape:
                    n_with_escape += 1
            print(f"  SCC #{si+1} ({len(scc)}): {n_with_escape}/{len(scc)} configs have escape move")


if __name__ == "__main__":
    main()
