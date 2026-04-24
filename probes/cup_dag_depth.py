#!/usr/bin/env python3
"""CUP: Compute DAG depth of bad→bad graph and analyze the rank function.

If we can find a closed-form expression for the DAG rank, that IS the potential.
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


def psi(c, n):
    d = get_d_vector(c, n)
    total = 0
    for i in range(n):
        if d[i] == 1:
            total += i
        elif d[i] == 2:
            total += (n - 1 - i)
    return total


def f_boundary(c_0, d_n1, n):
    table = {
        (0, 0): 0,
        (0, 1): -(3*n - 2),
        (0, 2): -(3*n - 3),
        (1, 0): 2*(n - 1),
        (1, 1): -n,
        (1, 2): -(n - 1),
    }
    return table[(c_0, d_n1)]


def compute_dag_ranks(n):
    """Compute DAG rank (longest path from each node) in the bad→bad graph."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Build adjacency list and reverse adjacency list
    adj = defaultdict(list)  # successors
    radj = defaultdict(list)  # predecessors
    in_degree = defaultdict(int)

    for c in bad_set:
        in_degree.setdefault(c, 0)
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ in bad_set:
                adj[c].append(succ)
                radj[succ].append(c)
                in_degree[succ] = in_degree.get(succ, 0) + 1

    # Topological sort + compute longest path (DAG rank)
    # rank[c] = longest path from c to a sink
    rank = {}
    # Process sinks first (no successors in bad set, or successors all go to good)
    queue = deque()
    out_degree = {}
    for c in bad_set:
        out_degree[c] = len(adj[c])
        if out_degree[c] == 0:
            rank[c] = 0
            queue.append(c)

    while queue:
        c = queue.popleft()
        for pred in radj[c]:
            if pred not in rank or rank[pred] < rank[c] + 1:
                rank[pred] = rank[c] + 1
            # We need a different approach - BFS from sinks isn't right for longest path

    # Correct approach: topological sort, then compute rank in reverse topo order
    # Kahn's algorithm for topo sort
    topo = []
    in_deg = dict(in_degree)
    q = deque([c for c in bad_set if in_deg.get(c, 0) == 0])
    while q:
        c = q.popleft()
        topo.append(c)
        for s in adj[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)

    if len(topo) != len(bad_set):
        print(f"  WARNING: SCC detected! Only {len(topo)}/{len(bad_set)} nodes in DAG")
        return None

    # Compute longest path from each node (process in reverse topo order)
    rank = {}
    for c in reversed(topo):
        if not adj[c]:
            rank[c] = 0
        else:
            rank[c] = max(rank[s] + 1 for s in adj[c])

    return rank, adj, bad_set, fs


def analyze_ranks(n):
    """Analyze the DAG rank function to find patterns."""
    result = compute_dag_ranks(n)
    if result is None:
        return
    rank, adj, bad_set, fs = result

    max_rank = max(rank.values())
    print(f"  DAG depth (max rank): {max_rank}")
    print(f"  Bad configs: {len(bad_set)}")

    # Rank distribution
    rank_dist = defaultdict(int)
    for c in bad_set:
        rank_dist[rank[c]] += 1

    # Rank vs fc
    rank_by_fc = defaultdict(list)
    for c in bad_set:
        fc = frontier_count(c, n)
        rank_by_fc[fc].append(rank[c])

    print(f"  Rank by fc level:")
    for fc in sorted(rank_by_fc.keys()):
        ranks = rank_by_fc[fc]
        print(f"    fc={fc}: count={len(ranks)}, "
              f"rank ∈ [{min(ranks)}, {max(ranks)}]")

    # Find the config with max rank (worst-case starting point)
    worst_configs = [c for c in bad_set if rank[c] == max_rank]
    print(f"\n  Worst-case configs (rank={max_rank}):")
    for c in worst_configs[:3]:
        d = get_d_vector(c, n)
        fc = frontier_count(c, n)
        ps = psi(c, n)
        fb = f_boundary(c[0], d[n-1], n)
        print(f"    c={c}, d={d}, fc={fc}, Ψ={ps}, f={fb}, Ψ+f={ps+fb}")

    # Correlate rank with Ψ+f and fc
    # Is rank well-predicted by A*fc + Ψ+f for some A?
    from collections import Counter
    best_corr = 0
    best_A = 0
    for A_try in range(0, 5*n):
        # Compute Φ = A*fc + Ψ+f for each config
        phi_vals = {}
        for c in bad_set:
            fc = frontier_count(c, n)
            d = get_d_vector(c, n)
            phi = A_try * fc + psi(c, n) + f_boundary(c[0], d[n-1], n)
            phi_vals[c] = phi
        # Check: does higher phi correlate with higher rank?
        # Count concordant pairs (among a sample)
        import random
        sample = random.sample(list(bad_set), min(500, len(bad_set)))
        concordant = 0
        discordant = 0
        for i in range(len(sample)):
            for j in range(i+1, min(i+10, len(sample))):
                ci, cj = sample[i], sample[j]
                dr = rank[ci] - rank[cj]
                dp = phi_vals[ci] - phi_vals[cj]
                if dr * dp > 0:
                    concordant += 1
                elif dr * dp < 0:
                    discordant += 1
        if concordant + discordant > 0:
            tau = (concordant - discordant) / (concordant + discordant)
            if tau > best_corr:
                best_corr = tau
                best_A = A_try

    print(f"\n  Best correlation with A*fc + Ψ+f: A={best_A}, τ={best_corr:.4f}")

    # Trace the worst-case path
    print(f"\n  Worst-case path (first 15 steps):")
    c = worst_configs[0]
    for step in range(min(15, max_rank)):
        d = get_d_vector(c, n)
        fc = frontier_count(c, n)
        print(f"    step {step}: rank={rank[c]:3d} fc={fc} d={d} c0={c[0]}", end='')
        # Find successor with highest rank (longest path)
        best_succ = None
        best_proc = None
        for s in adj[c]:
            if best_succ is None or rank[s] > rank[best_succ]:
                best_succ = s
                best_proc = None
                # Find which processor moved
                for i in range(n):
                    if c[i] != s[i]:
                        best_proc = i
                        break
        if best_succ:
            mt = "BOT" if best_proc == 0 else ("TOP" if best_proc == n-1 else f"M{best_proc}")
            dfc = frontier_count(best_succ, n) - fc
            print(f"  → {mt} Δfc={dfc:+d}")
            c = best_succ
        else:
            print(f"  → GOOD")
            break


if __name__ == "__main__":
    for nv in range(3, 10):
        print(f"\nn={nv}:")
        analyze_ranks(nv)
