#!/usr/bin/env python3
"""Convergence proof investigation — Part 4.

KEY IDEA: Partition by boundary values and show DAG within each partition.
If we fix c[0], then P0 never fires, and the system is a chain with a fixed
left boundary. Test whether each such restricted graph is a DAG.

Then analyze the cross-partition transitions.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import deque, defaultdict, Counter
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system


def get_full_graph(n):
    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(c for c in all_configs if c not in good_set)
    return ms, fs, good_set, bad_set


def check_dag(configs, adj_func):
    """Check if the directed graph on configs (given by adj_func) is a DAG.
    adj_func(c) returns list of successors."""
    in_deg = {c: 0 for c in configs}
    adj = {c: [] for c in configs}
    for c in configs:
        for s in adj_func(c):
            if s in in_deg:
                adj[c].append(s)
                in_deg[s] += 1
    q = deque(c for c in configs if in_deg[c] == 0)
    processed = 0
    while q:
        c = q.popleft()
        processed += 1
        for s in adj[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)
    return processed == len(configs)


def find_scc(configs, adj_func):
    """Find strongly connected components via Tarjan's algorithm.
    Returns list of SCCs with size > 1 (cycles)."""
    index_counter = [0]
    stack = []
    lowlink = {}
    index = {}
    on_stack = set()
    sccs = []

    adj_cache = {}
    config_set = set(configs)
    for c in configs:
        adj_cache[c] = [s for s in adj_func(c) if s in config_set]

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)

        for w in adj_cache[v]:
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index[w])

        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                scc.append(w)
                if w == v:
                    break
            if len(scc) > 1:
                sccs.append(scc)

    # Use iterative version to avoid recursion limit
    sys.setrecursionlimit(100000)
    for v in configs:
        if v not in index:
            strongconnect(v)

    return sccs


def main():
    # ================================================================
    # PART 1: FIX c[0] AND CHECK DAG
    # ================================================================
    print("=" * 90)
    print("PART 1: FIX BOUNDARY VALUE c[0] — CHECK DAG PROPERTY")
    print("=" * 90)

    for nv in range(5, 13):
        ms, fs, good_set, bad_set = get_full_graph(nv)
        n = nv

        def get_successors_except_p0(c):
            succs = []
            for i in range(1, n):  # Skip P0
                L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c)
                    lst[i] = new_S
                    succ = tuple(lst)
                    if succ in bad_set:
                        succs.append(succ)
            return succs

        for v0 in range(2):
            partition = set(c for c in bad_set if c[0] == v0)
            is_dag = check_dag(partition, get_successors_except_p0)
            print(f"  n={nv}, c[0]={v0}: {len(partition)} configs, "
                  f"DAG (P0 frozen)? {'YES' if is_dag else '*** NO ***'}")
            if not is_dag:
                # Find cycles
                sccs = find_scc(list(partition), get_successors_except_p0)
                print(f"    Found {len(sccs)} non-trivial SCCs!")
                for scc in sccs[:3]:
                    print(f"    SCC of size {len(scc)}: {scc[:5]}...")

        if 4 * 3 ** (nv - 2) > 500000:
            break

    # ================================================================
    # PART 2: FIX c[n-1] AND CHECK DAG
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 2: FIX c[n-1] — CHECK DAG PROPERTY")
    print("=" * 90)

    for nv in range(5, 13):
        ms, fs, good_set, bad_set = get_full_graph(nv)
        n = nv

        def get_successors_except_pn(c):
            succs = []
            for i in range(n - 1):  # Skip P_{n-1}
                L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c)
                    lst[i] = new_S
                    succ = tuple(lst)
                    if succ in bad_set:
                        succs.append(succ)
            return succs

        for vn in range(2):
            partition = set(c for c in bad_set if c[n-1] == vn)
            is_dag = check_dag(partition, get_successors_except_pn)
            print(f"  n={nv}, c[{n-1}]={vn}: {len(partition)} configs, "
                  f"DAG (P{n-1} frozen)? {'YES' if is_dag else '*** NO ***'}")
            if not is_dag:
                sccs = find_scc(list(partition), get_successors_except_pn)
                print(f"    Found {len(sccs)} non-trivial SCCs!")

        if 4 * 3 ** (nv - 2) > 500000:
            break

    # ================================================================
    # PART 3: FIX BOTH BOUNDARIES
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 3: FIX BOTH BOUNDARIES c[0] AND c[n-1]")
    print("=" * 90)

    for nv in range(5, 13):
        ms, fs, good_set, bad_set = get_full_graph(nv)
        n = nv

        def get_successors_interior(c):
            succs = []
            for i in range(1, n - 1):  # Skip P0 and P_{n-1}
                L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c)
                    lst[i] = new_S
                    succ = tuple(lst)
                    if succ in bad_set:
                        succs.append(succ)
            return succs

        all_dag = True
        for v0 in range(2):
            for vn in range(2):
                partition = set(c for c in bad_set if c[0] == v0 and c[n-1] == vn)
                if not partition:
                    continue
                is_dag = check_dag(partition, get_successors_interior)
                status = "YES" if is_dag else "*** NO ***"
                if not is_dag:
                    all_dag = False
                    sccs = find_scc(list(partition), get_successors_interior)
                    print(f"  n={nv}, c[0]={v0}, c[{n-1}]={vn}: {len(partition)} configs, "
                          f"DAG? {status} — {len(sccs)} SCCs")
                    for scc in sccs[:2]:
                        print(f"    SCC: {scc[:4]}")
                else:
                    print(f"  n={nv}, c[0]={v0}, c[{n-1}]={vn}: {len(partition)} configs, DAG? YES")

        if 4 * 3 ** (nv - 2) > 500000:
            break

    # ================================================================
    # PART 4: PROGRESSIVELY FREEZE POSITIONS
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 4: PROGRESSIVELY FREEZE POSITIONS")
    print("=" * 90)
    print("Which positions can we freeze (exclude from firing) and still have DAG?")

    for nv in [6, 7, 8]:
        ms, fs, good_set, bad_set = get_full_graph(nv)
        n = nv

        # Try freezing single positions
        print(f"\nn={nv}:")
        for freeze_pos in range(n):
            def get_succs(c, fp=freeze_pos):
                succs = []
                for i in range(n):
                    if i == fp:
                        continue
                    L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                    new_S = fs[i](L, S, R)
                    if new_S != S:
                        lst = list(c); lst[i] = new_S; succ = tuple(lst)
                        if succ in bad_set:
                            succs.append(succ)
                return succs

            is_dag = check_dag(bad_set, get_succs)
            print(f"  Freeze P{freeze_pos}: DAG? {'YES' if is_dag else 'NO'}")
            if not is_dag:
                sccs = find_scc(list(bad_set), get_succs)
                total_in_sccs = sum(len(s) for s in sccs)
                print(f"    {len(sccs)} SCCs, total {total_in_sccs} configs in cycles")

    # ================================================================
    # PART 5: FREEZE PAIRS
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 5: FREEZE POSITION PAIRS — WHICH PAIRS BREAK CYCLES?")
    print("=" * 90)

    for nv in [6, 7]:
        ms, fs, good_set, bad_set = get_full_graph(nv)
        n = nv
        print(f"\nn={nv}:")

        # For positions that don't give DAG when frozen alone,
        # try freezing pairs
        for f1 in range(n):
            for f2 in range(f1 + 1, n):
                def get_succs(c, fp1=f1, fp2=f2):
                    succs = []
                    for i in range(n):
                        if i == fp1 or i == fp2:
                            continue
                        L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                        new_S = fs[i](L, S, R)
                        if new_S != S:
                            lst = list(c); lst[i] = new_S; succ = tuple(lst)
                            if succ in bad_set:
                                succs.append(succ)
                    return succs

                is_dag = check_dag(bad_set, get_succs)
                if not is_dag:
                    sccs = find_scc(list(bad_set), get_succs)
                    total = sum(len(s) for s in sccs)
                    print(f"  Freeze (P{f1}, P{f2}): NO — "
                          f"{len(sccs)} SCCs, {total} in cycles")
                else:
                    print(f"  Freeze (P{f1}, P{f2}): YES")

    # ================================================================
    # PART 6: CHARACTERIZE CYCLES WHEN FREEZING ONE POSITION
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 6: CYCLE CHARACTERIZATION WHEN FREEZING P0")
    print("=" * 90)

    for nv in [6, 7]:
        ms, fs, good_set, bad_set = get_full_graph(nv)
        n = nv

        def get_succs_no_p0(c):
            succs = []
            for i in range(1, n):
                L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c); lst[i] = new_S; succ = tuple(lst)
                    if succ in bad_set:
                        succs.append(succ)
            return succs

        sccs = find_scc(list(bad_set), get_succs_no_p0)

        if sccs:
            print(f"\nn={nv}: {len(sccs)} SCCs when P0 frozen")
            # Analyze the first few SCCs
            for idx, scc in enumerate(sccs[:5]):
                scc_set = set(scc)
                print(f"\n  SCC {idx}: {len(scc)} configs")
                # What boundary values appear?
                b_vals = Counter(c[0] for c in scc)
                e_vals = Counter(c[n-1] for c in scc)
                print(f"    c[0] values: {dict(b_vals)}")
                print(f"    c[{n-1}] values: {dict(e_vals)}")

                # Show a few configs and their transitions
                c0 = scc[0]
                print(f"    Example config: {c0}")
                succs = [s for s in get_succs_no_p0(c0) if s in scc_set]
                for s in succs[:3]:
                    # Which position changed?
                    for i in range(n):
                        if c0[i] != s[i]:
                            print(f"      → {s} via P{i} ({c0[i]}→{s[i]})")
                            break

                # Try to trace a cycle within this SCC
                visited = set()
                path = [c0]
                visited.add(c0)
                current = c0
                found_cycle = False
                for _ in range(len(scc) * 2):
                    succs_in_scc = [s for s in get_succs_no_p0(current) if s in scc_set]
                    if not succs_in_scc:
                        break
                    # Follow first unvisited, or first if all visited
                    nxt = None
                    for s in succs_in_scc:
                        if s not in visited:
                            nxt = s
                            break
                    if nxt is None:
                        nxt = succs_in_scc[0]
                        if nxt == c0 and len(path) > 1:
                            found_cycle = True
                            break
                        elif nxt in visited:
                            # Find which config it matches
                            if nxt == c0:
                                found_cycle = True
                                break
                            break
                    visited.add(nxt)
                    path.append(nxt)
                    current = nxt

                if found_cycle:
                    print(f"    Traced cycle of length {len(path)}")
                    for i, c in enumerate(path[:10]):
                        if i < len(path) - 1:
                            for p in range(n):
                                if c[p] != path[i+1][p]:
                                    print(f"      {c} →[P{p}] ({c[p]}→{path[i+1][p]})")
                                    break
                        else:
                            print(f"      {c} → cycle back to start")
        else:
            print(f"\nn={nv}: NO SCCs when P0 frozen (all DAG)")

    # ================================================================
    # PART 7: TEST FREEZING P0 + PARTITIONING BY c[0]
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 7: FREEZE P0 AND PARTITION BY c[0]")
    print("=" * 90)

    for nv in range(5, 13):
        ms, fs, good_set, bad_set = get_full_graph(nv)
        n = nv

        def get_succs_no_p0(c):
            succs = []
            for i in range(1, n):
                L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c); lst[i] = new_S; succ = tuple(lst)
                    if succ in bad_set:
                        succs.append(succ)
            return succs

        # Note: when P0 is frozen, c[0] doesn't change.
        # But transitions at P1 can produce configs with any c[1] value,
        # and transitions at P_{n-1} can change c[n-1].
        # So partitioning by c[0] and freezing P0 means we're in a
        # fixed-boundary-on-left chain.

        for v0 in range(2):
            partition = [c for c in bad_set if c[0] == v0]
            # In this partition, P0 is frozen at v0. Transitions only at P1,...,P_{n-1}.
            # c[0] never changes (P0 frozen).
            is_dag = check_dag(set(partition), get_succs_no_p0)
            print(f"  n={nv}, c[0]={v0}, P0 frozen: {len(partition)} configs, "
                  f"DAG? {'YES' if is_dag else 'NO'}")
            if not is_dag:
                sccs = find_scc(partition, get_succs_no_p0)
                print(f"    {len(sccs)} SCCs")

        if 4 * 3 ** (nv - 2) > 500000:
            break


if __name__ == "__main__":
    main()
