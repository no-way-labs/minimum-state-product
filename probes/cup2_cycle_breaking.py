#!/usr/bin/env python3
"""Find cycles in the copy-only variant and understand how anomalous
entries break them.

With T_mid(2,1,1)=2 (copy_L instead of anomalous 0), the bad graph has
cycles. Find these cycles and check which ones are broken by:
  T_mid(2,1,1)=0 (the anomalous liveness fix)
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top
from verifier import verify_system
from itertools import product as cartesian
from collections import deque


def build_with_mid_fix(nv, mid_211_val):
    """Build system with specified T_mid(2,1,1) value."""
    t_mid = dict(T_mid)
    t_mid[(2,1,1)] = mid_211_val

    n = nv
    ms = [2] + [3] * (n - 2) + [2]

    def make_func(tbl):
        def f(L, S, R):
            return tbl.get((L, S, R), S)
        return f

    fs = []
    for i in range(n):
        if i == 0:
            fs.append(make_func(T_bot))
        elif i == 1:
            fs.append(make_func(T_low))
        elif i == n - 2:
            fs.append(make_func(T_high))
        elif i == n - 1:
            fs.append(make_func(T_top))
        else:
            fs.append(make_func(t_mid))

    return ms, fs


def find_cycles(adj, nodes):
    """Find all strongly connected components with >1 node."""
    # Tarjan's SCC
    index_counter = [0]
    stack = []
    lowlink = {}
    index = {}
    on_stack = {}
    sccs = []

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack[v] = True

        for w in adj.get(v, []):
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif on_stack.get(w, False):
                lowlink[v] = min(lowlink[v], index[w])

        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack[w] = False
                scc.append(w)
                if w == v:
                    break
            if len(scc) > 1:
                sccs.append(scc)

    for v in nodes:
        if v not in index:
            strongconnect(v)

    return sccs


def main():
    print("CYCLE-BREAKING ANALYSIS")
    print("=" * 70)

    # Find cycles with T_mid(2,1,1)=2 (copy_L, DAG=N)
    for nv in range(5, 10):
        prod = 4 * 3 ** (nv - 2)
        if prod > 30000:
            break

        # Copy-only variant: T_mid(2,1,1)=2
        ms_alt, fs_alt = build_with_mid_fix(nv, 2)
        result_alt = verify_system(ms_alt, fs_alt)
        good_alt = result_alt['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms_alt)))
        bad_alt = set(c for c in all_configs if c not in good_alt)

        # Build bad-config transition graph for copy-only variant
        adj_alt = {c: [] for c in bad_alt}
        for c in bad_alt:
            for i in range(nv):
                Li = c[(i-1)%nv]; Si = c[i]; Ri = c[(i+1)%nv]
                out = fs_alt[i](Li, Si, Ri)
                if out != Si:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_alt:
                        adj_alt[c].append(succ)

        sccs = find_cycles(adj_alt, bad_alt)
        total_in_sccs = sum(len(s) for s in sccs)
        print(f"\nn={nv} [T_mid(2,1,1)=2]: {len(sccs)} SCCs with cycles, "
              f"{total_in_sccs} configs in cycles")

        # Show the smallest SCCs
        for scc in sorted(sccs, key=len)[:3]:
            print(f"  SCC size={len(scc)}:")
            for c in sorted(scc)[:5]:
                fc = sum(1 for j in range(nv) if c[j] != c[(j+1)%nv])
                print(f"    {c} fc={fc}")
            if len(scc) > 5:
                print(f"    ... and {len(scc)-5} more")

        # For each SCC, find a minimal cycle
        if sccs:
            smallest_scc = min(sccs, key=len)
            scc_set = set(smallest_scc)
            # BFS from first node to find a cycle
            start = smallest_scc[0]
            parent = {start: None}
            queue = deque([start])
            cycle_found = None
            while queue and cycle_found is None:
                cur = queue.popleft()
                for s in adj_alt[cur]:
                    if s == start and parent[cur] is not None:
                        # Found cycle!
                        path = [start]
                        node = cur
                        while node != start:
                            path.append(node)
                            node = parent[node]
                        path.reverse()
                        cycle_found = path
                        break
                    if s in scc_set and s not in parent:
                        parent[s] = cur
                        queue.append(s)

            if cycle_found:
                print(f"\n  Minimal cycle (length {len(cycle_found)}):")
                for j, c in enumerate(cycle_found):
                    next_c = cycle_found[(j+1)%len(cycle_found)]
                    # Find which position changed
                    for i in range(nv):
                        if c[i] != next_c[i]:
                            fc = sum(1 for k in range(nv) if c[k] != c[(k+1)%nv])
                            print(f"    {c} →[P{i}]→ fc={fc}")
                            break

                # Check: does the original system (T_mid(2,1,1)=0) break this cycle?
                ms_orig, fs_orig = build_with_mid_fix(nv, 0)
                result_orig = verify_system(ms_orig, fs_orig)
                good_orig = result_orig['good_configs']

                print(f"\n  Same cycle in original system (T_mid(2,1,1)=0):")
                for j, c in enumerate(cycle_found):
                    in_good = c in good_orig
                    # Check if each config still transitions to the next
                    next_c = cycle_found[(j+1)%len(cycle_found)]
                    edge_exists = False
                    for i in range(nv):
                        Li = c[(i-1)%nv]; Si = c[i]; Ri = c[(i+1)%nv]
                        out = fs_orig[i](Li, Si, Ri)
                        if out != Si:
                            lst = list(c); lst[i] = out; succ = tuple(lst)
                            if succ == next_c:
                                edge_exists = True
                                break
                    status = "GOOD" if in_good else "bad"
                    edge_status = "edge exists" if edge_exists else "EDGE BROKEN"
                    # Check if the T_mid(2,1,1) entry matters here
                    mid_matters = False
                    for i in range(2, nv-2):
                        if c[i-1]==2 and c[i]==1 and c[i+1]==1:
                            mid_matters = True
                    mid_note = " [MID(2,1,1) relevant]" if mid_matters else ""
                    print(f"    {c} {status}, {edge_status}{mid_note}")

    # KEY: Check which cycle edges are broken by T_mid(2,1,1)=0
    print("\n\nEDGE-LEVEL ANALYSIS: which cycle edges change?")
    print("-" * 60)
    for nv in [5, 6]:
        ms_alt, fs_alt = build_with_mid_fix(nv, 2)
        ms_orig, fs_orig = build_with_mid_fix(nv, 0)
        result_alt = verify_system(ms_alt, fs_alt)
        result_orig = verify_system(ms_orig, fs_orig)
        good_alt = result_alt['good_configs']
        good_orig = result_orig['good_configs']

        all_configs = list(cartesian(*(range(m) for m in ms_alt)))
        bad_alt = set(c for c in all_configs if c not in good_alt)

        # Find all edges in alt that DON'T exist in orig (or go to different target)
        changed_edges = 0
        for c in bad_alt:
            for i in range(nv):
                Li = c[(i-1)%nv]; Si = c[i]; Ri = c[(i+1)%nv]
                out_alt = fs_alt[i](Li, Si, Ri)
                out_orig = fs_orig[i](Li, Si, Ri)
                if out_alt != out_orig:
                    changed_edges += 1
                    if changed_edges <= 10:
                        print(f"  n={nv}: {c} P{i}: alt→{out_alt}, orig→{out_orig} "
                              f"(L={Li},S={Si},R={Ri})")

        print(f"  n={nv}: {changed_edges} edges changed by T_mid(2,1,1): 2→0")


if __name__ == "__main__":
    main()
