#!/usr/bin/env python3
"""CUP: Deep analysis of cycle obstructions.

Key question: What structural property prevents bad cycles?

Approach: For each pair of bad configs (c, c') where c→...→c' and c'→...→c
both exist, what property is violated? Track:
1. c_0 parity through cycles
2. Frontier count along paths
3. d-vector constraints from top reset
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system
from collections import defaultdict, deque


def sol3_v1_rules(ms, n):
    def make_bottom(m0):
        def f(L, S, R):
            if (S + 1) % m0 == R % m0:
                return (S - 1) % m0
            return S
        return f
    def make_top(m_top):
        def f(L, S, R):
            if L % m_top == R % m_top and (L % m_top + 1) % m_top != S:
                return (L % m_top + 1) % m_top
            return S
        return f
    def make_middle(m_i):
        def f(L, S, R):
            if (S + 1) % m_i == L % m_i:
                return L % m_i
            if (S + 1) % m_i == R % m_i:
                return R % m_i
            return S
        return f
    fs = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n - 1]))
    return fs


def get_privileged(c, fs, n):
    priv = []
    for i in range(n):
        L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
        if fs[i](L, S, R) != S:
            priv.append(i)
    return priv


def apply_move(c, i, fs, n):
    L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
    lst = list(c); lst[i] = fs[i](L, S, R); return tuple(lst)


def frontier_count(c, n):
    return sum(1 for i in range(n) if (c[(i+1) % n] - c[i]) % 3 != 0)


def get_d_vector(c, n):
    return tuple((c[(i+1)%n] - c[i]) % 3 for i in range(n))


# =======================================================================
# KEY TEST: In any path that returns c_0 to start, does fc strictly decrease?
# If so, no cycle exists (since c_0 must return in a cycle).
# =======================================================================

def test_c0_return_fc_decrease(n):
    """For each bad config c, find all bad configs c' reachable from c
    with c'[0] = c[0] and fc(c') >= fc(c). If none: the property holds."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Build bad→bad graph
    graph = defaultdict(list)
    for c in bad_set:
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ in bad_set:
                graph[c].append(succ)

    # For each bad config c, BFS to find all reachable bad configs c'
    # with c'[0] = c[0] and fc(c') >= fc(c).
    violations = []
    for c in sorted(bad_set):
        fc_c = frontier_count(c, n)
        c0 = c[0]
        # BFS
        visited = {c}
        queue = deque([c])
        while queue:
            cur = queue.popleft()
            for nxt in graph[cur]:
                if nxt in visited:
                    continue
                visited.add(nxt)
                if nxt[0] == c0 and frontier_count(nxt, n) >= fc_c and nxt != c:
                    violations.append((c, nxt, frontier_count(nxt, n)))
                queue.append(nxt)

    if violations:
        print(f"  n={n}: c0-return-fc-decrease FAILS. {len(violations)} violations.")
        for c, cp, fc_cp in violations[:5]:
            d = get_d_vector(c, n)
            dp = get_d_vector(cp, n)
            print(f"    {c} fc={frontier_count(c,n)} d={d} → {cp} fc={fc_cp} d={dp}")
    else:
        print(f"  n={n}: c0-return-fc-decrease HOLDS ✓")
    return len(violations) == 0


# =======================================================================
# Try a more refined potential: (fc, c_0, c_{n-1})
# Track whether any bad config can reach another with same (fc, c_0, c_{n-1})
# =======================================================================

def test_triple_return(n):
    """In a cycle, (fc, c_0, c_{n-1}) must all return. Does (c_0, c_{n-1}) return
    force fc to decrease?"""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    graph = defaultdict(list)
    for c in bad_set:
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ in bad_set:
                graph[c].append(succ)

    violations = []
    for c in sorted(bad_set):
        fc_c = frontier_count(c, n)
        c0 = c[0]
        cn1 = c[n-1]
        visited = {c}
        queue = deque([c])
        while queue:
            cur = queue.popleft()
            for nxt in graph[cur]:
                if nxt in visited:
                    continue
                visited.add(nxt)
                if nxt[0] == c0 and nxt[n-1] == cn1 and frontier_count(nxt, n) >= fc_c and nxt != c:
                    violations.append((c, nxt))
                queue.append(nxt)

    if violations:
        print(f"  n={n}: (c0,c{{n-1}})-return-fc-decrease FAILS. {len(violations)} violations.")
        for c, cp in violations[:5]:
            print(f"    {c} fc={frontier_count(c,n)} → {cp} fc={frontier_count(cp,n)}")
    else:
        print(f"  n={n}: (c0,c{{n-1}})-return-fc-decrease HOLDS ✓")
    return len(violations) == 0


# =======================================================================
# CRITICAL: Check if there's a bad config reachable from itself (cycle check)
# with intermediate depth. For this, find SCCs efficiently.
# =======================================================================

def find_bad_sccs(n):
    """Find strongly connected components in bad→bad graph using Tarjan's."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    graph = defaultdict(list)
    for c in bad_set:
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ in bad_set:
                graph[c].append(succ)

    # Iterative Tarjan's SCC
    index_counter = [0]
    stack = []
    on_stack = set()
    index = {}
    lowlink = {}
    sccs = []

    def strongconnect(v):
        work = [(v, 0)]  # (node, neighbor_index)
        index[v] = lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)

        while work:
            node, ni = work[-1]
            neighbors = graph[node]
            if ni < len(neighbors):
                work[-1] = (node, ni + 1)
                w = neighbors[ni]
                if w not in index:
                    index[w] = lowlink[w] = index_counter[0]
                    index_counter[0] += 1
                    stack.append(w)
                    on_stack.add(w)
                    work.append((w, 0))
                elif w in on_stack:
                    lowlink[node] = min(lowlink[node], index[w])
            else:
                if lowlink[node] == index[node]:
                    scc = []
                    while True:
                        w = stack.pop()
                        on_stack.discard(w)
                        scc.append(w)
                        if w == node:
                            break
                    sccs.append(scc)
                work.pop()
                if work:
                    parent = work[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[node])

    for v in bad_set:
        if v not in index:
            strongconnect(v)

    nontrivial = [s for s in sccs if len(s) > 1]
    # Also check self-loops
    self_loops = sum(1 for c in bad_set if c in graph[c])

    print(f"  n={n}: {len(bad_set)} bad configs, "
          f"{len(sccs)} SCCs, {len(nontrivial)} non-trivial SCCs, "
          f"{self_loops} self-loops")
    if nontrivial:
        for scc in nontrivial[:3]:
            print(f"    SCC of size {len(scc)}: {scc[:3]}...")
    return len(nontrivial) == 0 and self_loops == 0


# =======================================================================
# KEY STRUCTURAL CLAIM: For every bad config, the WORST-case number of
# steps to fc decrease is bounded by some function of n.
# Under ANY daemon, fc must decrease within B(n) steps.
# =======================================================================

def worst_case_fc_decrease(n):
    """For each bad config c, what is the maximum number of steps before
    fc MUST decrease (under adversarial daemon)?

    This is: max over all paths from c where fc never drops below fc(c),
    what is the longest such path?
    """
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # For each fc level, find the configs at that level
    by_fc = defaultdict(set)
    for c in bad_set:
        by_fc[frontier_count(c, n)].add(c)

    # For each fc level k, find the worst-case number of steps
    # to leave the set {c : fc(c) >= k} ∩ bad_set.
    # This is the max rank in the subgraph restricted to fc >= k.

    for k in sorted(by_fc.keys()):
        if k == 0:
            continue
        level_set = set()
        for kk in range(k, n + 1):
            level_set |= by_fc.get(kk, set())

        # Build subgraph within level_set
        sub_graph = defaultdict(list)
        for c in level_set:
            priv = get_privileged(c, fs, n)
            for p in priv:
                succ = apply_move(c, p, fs, n)
                if succ in level_set:
                    sub_graph[c].append(succ)

        # Check for cycles in this subgraph (should be DAG)
        # Compute longest path = worst-case steps to exit
        # Using iterative topo sort + longest path

        in_deg = defaultdict(int)
        for c in level_set:
            if c not in in_deg:
                in_deg[c] = 0
            for s in sub_graph[c]:
                in_deg[s] += 1

        queue = deque()
        for c in level_set:
            if in_deg[c] == 0:
                queue.append(c)

        longest = {}
        processed = 0
        while queue:
            c = queue.popleft()
            processed += 1
            if c not in longest:
                longest[c] = 0
            for s in sub_graph[c]:
                longest[s] = max(longest.get(s, 0), longest[c] + 1)
                in_deg[s] -= 1
                if in_deg[s] == 0:
                    queue.append(s)

        has_cycle = processed < len(level_set)
        max_len = max(longest.values()) if longest else 0
        print(f"    fc>={k}: {len(level_set)} configs, max_steps={max_len}, "
              f"{'CYCLE!' if has_cycle else 'DAG ✓'}")


# =======================================================================
# TRACKING EXPERIMENT: For worst-case paths, trace the sequence of
# (fc, c_0, d_{n-2}, d_{n-1}, move_type) to find the pattern.
# =======================================================================

def trace_worst_paths(n, max_traces=5):
    """Find and trace the worst-case convergence paths."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Build full transition graph
    graph = defaultdict(list)
    for c in bad_set:
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ in bad_set:
                graph[c].append((p, succ))
            else:
                graph[c].append((p, None))  # exits to good

    # Compute worst-case rank
    rank = {}
    parent = {}  # (config, move_index) that achieves worst rank
    changed = True
    while changed:
        changed = False
        for c in bad_set:
            if c in rank:
                continue
            priv = get_privileged(c, fs, n)
            worst = 0
            worst_move = None
            all_resolved = True
            for idx, p in enumerate(priv):
                succ = apply_move(c, p, fs, n)
                if succ in good_set:
                    steps = 1
                elif succ in rank:
                    steps = 1 + rank[succ]
                else:
                    all_resolved = False
                    break
                if steps > worst:
                    worst = steps
                    worst_move = (p, succ if succ in bad_set else None)
            if all_resolved:
                rank[c] = worst
                parent[c] = worst_move
                changed = True

    if not rank:
        return

    max_rank = max(rank.values())
    max_configs = [c for c, r in rank.items() if r == max_rank]

    print(f"\n  n={n}: max rank = {max_rank}, {len(max_configs)} max-rank configs")

    # Trace worst-case path from a max-rank config
    for c in sorted(max_configs)[:max_traces]:
        print(f"\n  Worst-case path from {c} (rank={rank[c]}):")
        cur = c
        step = 0
        while cur is not None and cur in bad_set and step <= max_rank:
            fc = frontier_count(cur, n)
            d = get_d_vector(cur, n)
            priv = get_privileged(cur, fs, n)
            if cur not in parent or parent[cur] is None:
                break
            p, nxt = parent[cur]
            mtype = "BOT" if p == 0 else ("TOP" if p == n-1 else f"M{p}")
            fc_nxt = frontier_count(nxt, n) if nxt else "G"
            print(f"    [{step:2d}] c0={cur[0]} cn={cur[n-1]} fc={fc} d={d} "
                  f"→ {mtype} → fc={fc_nxt}")
            cur = nxt
            step += 1
        if cur is not None and cur in good_set:
            print(f"    [{step:2d}] GOOD: {cur}")
        elif cur is not None:
            fc = frontier_count(cur, n)
            print(f"    [{step:2d}] c0={cur[0]} cn={cur[n-1]} fc={fc} → exit to good")
        break  # Just trace one


if __name__ == "__main__":
    print("=" * 60)
    print("SCC CHECK (no bad cycles)")
    print("=" * 60)
    for nv in range(3, 11):
        find_bad_sccs(nv)

    print("\n" + "=" * 60)
    print("c0-RETURN IMPLIES fc DECREASE?")
    print("=" * 60)
    for nv in range(3, 8):
        test_c0_return_fc_decrease(nv)

    print("\n" + "=" * 60)
    print("(c0, c_{n-1})-RETURN IMPLIES fc DECREASE?")
    print("=" * 60)
    for nv in range(3, 8):
        test_triple_return(nv)

    print("\n" + "=" * 60)
    print("WORST-CASE STEPS TO fc DECREASE (by level)")
    print("=" * 60)
    for nv in [4, 5, 6, 7]:
        print(f"\n  n={nv}:")
        worst_case_fc_decrease(nv)

    print("\n" + "=" * 60)
    print("WORST-CASE PATH TRACES")
    print("=" * 60)
    for nv in [5, 6]:
        trace_worst_paths(nv, max_traces=1)
