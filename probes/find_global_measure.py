#!/usr/bin/env python3
"""
Search for a single measure mu: Config -> Nat that strictly decreases on ALL bad steps.
This would bypass the need for FutureFc entirely.

Test with n=5 first (small: ms=(2,3,3,3,2), 108 configs).
"""

from itertools import product as cartesian
from collections import defaultdict

# LEAN TABLES
def TBotVal(L,S,R):
    t = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,
         (1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    return t.get((L,S,R), 0)
def TLowVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,
         (0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
         (1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    return t.get((L,S,R), 0)
def TMidVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,
         (0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
         (1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,
         (2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,
         (2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R), 0)
def THighVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,
         (1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,
         (2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    return t.get((L,S,R), 0)
def TTopVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,
         (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,
         (2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    return t.get((L,S,R), 0)

def make_system(n):
    ms = [2] + [3]*(n-2) + [2]

    def get_table(i):
        if i == 0: return TBotVal
        elif i == 1: return TLowVal
        elif i + 1 == n: return TTopVal
        elif i + 2 == n: return THighVal
        else: return TMidVal

    def fc(c):
        return sum(1 for j in range(n) if c[j] != c[(j+1)%n])

    def step(c, i):
        L = c[(i-1) % n]
        S = c[i]
        R = c[(i+1) % n]
        out = get_table(i)(L, S, R)
        if out != S:
            new_c = list(c)
            new_c[i] = out
            return tuple(new_c)
        return None

    all_configs = list(cartesian(*(range(m) for m in ms)))

    # Build transition graph
    all_succ = defaultdict(list)
    for c in all_configs:
        for i in range(n):
            succ = step(c, i)
            if succ is not None:
                all_succ[c].append(succ)

    # Find good cycle (terminal SCC)
    def tarjan(nodes, adj):
        idx = [0]; stack = []; lowlink = {}; index_map = {}; on_stack = set(); sccs = []
        for start in nodes:
            if start in index_map: continue
            cs = [(start, iter(adj.get(start, [])))]
            index_map[start] = lowlink[start] = idx[0]; idx[0] += 1
            stack.append(start); on_stack.add(start)
            while cs:
                v, ch = cs[-1]
                try:
                    w = next(ch)
                    if w not in index_map:
                        index_map[w] = lowlink[w] = idx[0]; idx[0] += 1
                        stack.append(w); on_stack.add(w)
                        cs.append((w, iter(adj.get(w, []))))
                    elif w in on_stack:
                        lowlink[v] = min(lowlink[v], index_map[w])
                except StopIteration:
                    cs.pop()
                    if cs: lowlink[cs[-1][0]] = min(lowlink[cs[-1][0]], lowlink[v])
                    if lowlink[v] == index_map[v]:
                        scc = []
                        while True:
                            w = stack.pop(); on_stack.discard(w); scc.append(w)
                            if w == v: break
                        sccs.append(scc)
        return sccs

    sccs = tarjan(all_configs, all_succ)
    terminal = []
    for i, scc in enumerate(sccs):
        scc_set = set(scc)
        if not any(w not in scc_set for v in scc for w in all_succ.get(v, [])):
            terminal.append(i)

    good_set = set(sccs[terminal[0]])
    bad_configs = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_configs)

    # Bad step graph (edges are (c, c') where c -> c' is a bad step)
    bad_edges = []
    for c in bad_configs:
        for succ in all_succ.get(c, []):
            if succ in bad_set:
                bad_edges.append((c, succ))

    return bad_configs, bad_set, bad_edges, fc

# Start with n=5
for n in [5, 6, 7]:
    bad_configs, bad_set, bad_edges, fc_fn = make_system(n)
    print(f"\nn={n}: {len(bad_configs)} bad configs, {len(bad_edges)} bad edges")

    # Compute depth = length of longest path from each config (via BFS/DFS)
    # This IS a valid measure if the bad step graph is a DAG.
    # Check: is the bad step graph a DAG?

    # Build adjacency
    adj = defaultdict(list)
    for c, s in bad_edges:
        adj[c].append(s)

    # Check for cycles in the bad graph
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {c: WHITE for c in bad_configs}
    has_cycle = False

    for start in bad_configs:
        if color[start] != WHITE:
            continue
        stack = [(start, iter(adj.get(start, [])))]
        color[start] = GRAY
        while stack:
            v, ch = stack[-1]
            try:
                w = next(ch)
                if color[w] == GRAY:
                    has_cycle = True
                    break
                elif color[w] == WHITE:
                    color[w] = GRAY
                    stack.append((w, iter(adj.get(w, []))))
            except StopIteration:
                stack.pop()
                color[v] = BLACK
        if has_cycle:
            break

    print(f"  Bad step graph is DAG: {not has_cycle}")

    if not has_cycle:
        # Compute longest path (= rank in DAG)
        # This gives a valid WF measure
        from functools import lru_cache
        memo = {}
        def longest_path(c):
            if c in memo:
                return memo[c]
            memo[c] = -1  # mark visiting
            best = 0
            for s in adj.get(c, []):
                best = max(best, 1 + longest_path(s))
            memo[c] = best
            return best

        for c in bad_configs:
            longest_path(c)

        max_rank = max(memo[c] for c in bad_configs)
        print(f"  Max DAG rank: {max_rank}")

        # Verify: every bad edge c->s has rank(c) > rank(s)
        violations = sum(1 for c, s in bad_edges if memo[c] <= memo[s])
        print(f"  Rank violations: {violations}")
