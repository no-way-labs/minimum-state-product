#!/usr/bin/env python3
"""Check if the OLD table (TMidVal(2,1,1)=2) gives a valid self-stabilizing system."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import T_bot, T_low, T_high, T_top
from collections import deque

# OLD T_mid: TMidVal(2,1,1) = 2 (not 0)
T_mid_old = {
    (0,0,0): 0,  (0,0,1): 0,  (0,0,2): 0,
    (0,1,0): 0,  (0,1,1): 1,  (0,1,2): 0,
    (0,2,0): 0,  (0,2,1): 2,  (0,2,2): 0,
    (1,0,0): 1,  (1,0,1): 1,  (1,0,2): 1,
    (1,1,0): 1,  (1,1,1): 1,  (1,1,2): 2,
    (1,2,0): 0,  (1,2,1): 1,  (1,2,2): 2,
    (2,0,0): 0,  (2,0,1): 0,  (2,0,2): 2,
    (2,1,0): 1,  (2,1,1): 2,  (2,1,2): 2,  # KEY: (2,1,1)=2 instead of 0
    (2,2,0): 0,  (2,2,1): 2,  (2,2,2): 2,
}

def build_old_system(n):
    assert n >= 4
    ms = [2] + [3] * (n - 2) + [2]
    def make_f(table):
        def f(L, S, R): return table[(L, S, R)]
        return f
    if n == 4:
        fs = [make_f(T_bot), make_f(T_low), make_f(T_high), make_f(T_top)]
    elif n == 5:
        fs = [make_f(T_bot), make_f(T_low), make_f(T_mid_old),
              make_f(T_high), make_f(T_top)]
    else:
        fs = [make_f(T_bot), make_f(T_low)]
        for _ in range(2, n - 2):
            fs.append(make_f(T_mid_old))
        fs.append(make_f(T_high))
        fs.append(make_f(T_top))
    return ms, fs

def check_convergence(n):
    ms, fs = build_old_system(n)
    N = 1
    for m in ms: N *= m

    def idx_to_config(idx):
        c = []
        for m in reversed(ms):
            c.append(idx % m); idx //= m
        return tuple(reversed(c))

    def config_to_idx(c):
        idx = 0
        for j in range(n): idx = idx * ms[j] + c[j]
        return idx

    def move(c, pos):
        L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]
        c2 = list(c); c2[pos] = fs[pos](L, S, R); return tuple(c2)

    def fc(c):
        return sum(1 for j in range(n) if c[j] != c[(j+1)%n])

    # Check self-stabilization: from every config, can we reach a good config?
    # Good config: fc = 0
    # Build reverse adjacency and BFS from good configs
    all_configs = [idx_to_config(i) for i in range(N)]
    good = set()
    bad = set()
    for i in range(N):
        c = all_configs[i]
        if fc(c) == 0:
            good.add(i)
        else:
            bad.add(i)

    # Build adjacency: i → j means j is reachable from i by one privileged move
    adj = {i: [] for i in range(N)}
    for i in range(N):
        c = all_configs[i]
        for p in range(n):
            c2 = move(c, p)
            if c2 != c:
                j = config_to_idx(c2)
                adj[i].append(j)

    # Check: is the bad-step graph a DAG?
    # (Only considering bad → bad edges)
    bad_adj = {i: [] for i in bad}
    for i in bad:
        for j in adj[i]:
            if j in bad:
                bad_adj[i].append(j)

    # Topological sort (Kahn's algorithm)
    in_deg = {i: 0 for i in bad}
    for i in bad:
        for j in bad_adj[i]:
            in_deg[j] += 1

    q = deque(i for i in bad if in_deg[i] == 0)
    processed = 0
    while q:
        i = q.popleft()
        processed += 1
        for j in bad_adj[i]:
            in_deg[j] -= 1
            if in_deg[j] == 0:
                q.append(j)

    is_dag = processed == len(bad)

    # Also check: every bad config has at least one privileged move
    # (i.e., no deadlocked bad configs)
    deadlocked = []
    for i in bad:
        if len(adj[i]) == 0:
            deadlocked.append(i)
        # Also check: at least one move leads somewhere (even if to good)
        # Actually, we need: every bad config has a privileged processor
        c = all_configs[i]
        has_priv = any(move(c, p) != c for p in range(n))
        if not has_priv:
            deadlocked.append(i)

    # Check: can every bad config reach a good config?
    # BFS from all bad configs, checking reachability
    reaches_good = set()
    visited = set()
    # Start BFS from each bad config
    for start in bad:
        if start in reaches_good:
            continue
        path = set()
        stack = [start]
        while stack:
            node = stack.pop()
            if node in visited or node in reaches_good:
                if node in good or node in reaches_good:
                    reaches_good.update(path)
                continue
            visited.add(node)
            path.add(node)
            if node in good:
                reaches_good.update(path)
                continue
            for j in adj[node]:
                stack.append(j)

    # Actually let me do a simpler BFS from good configs backwards
    # Config i can reach good if there's a path from i to any good config
    can_reach_good = set(good)
    # Reverse BFS: if j ∈ can_reach_good and i → j, then i ∈ can_reach_good
    rev_adj = {i: [] for i in range(N)}
    for i in range(N):
        for j in adj[i]:
            rev_adj[j].append(i)
    q = deque(good)
    while q:
        j = q.popleft()
        for i in rev_adj[j]:
            if i not in can_reach_good:
                can_reach_good.add(i)
                q.append(i)

    not_reaching = bad - can_reach_good

    print(f"n={n}: {N} configs, {len(good)} good, {len(bad)} bad")
    print(f"  Bad-step DAG: {is_dag} (processed {processed}/{len(bad)})")
    print(f"  Deadlocked bad configs: {len(deadlocked)}")
    print(f"  Bad configs NOT reaching good: {len(not_reaching)}")
    if not_reaching:
        for i in sorted(not_reaching)[:5]:
            c = all_configs[i]
            print(f"    Config {c}, fc={fc(c)}")

    return is_dag and len(deadlocked) == 0 and len(not_reaching) == 0

print("Checking OLD table (TMidVal(2,1,1)=2):")
for n in [5, 6, 7, 8, 9]:
    valid = check_convergence(n)
    print(f"  Valid: {valid}\n")
