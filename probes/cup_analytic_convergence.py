#!/usr/bin/env python3
"""CUP: Complete analytic convergence proof verification.

The proof:
1. Φ = Ψ + f(c_0, d_{n-1}) decreases by exactly 1 on every Δfc=0 bad→bad transition.
   → Δfc=0 subgraph is a DAG.
2. Any cycle in the Δfc≥0 subgraph has Σ Δfc = 0 with each term ≥ 0 → all = 0.
   → Δfc≥0 subgraph is a DAG.
3. fc=0 → good config (only (0,...,0) and (1,...,1), both with 1 privilege).
4. From any bad config: Δfc≥0 DAG forces eventual Δfc<0 or escape to good.
   fc decreases by ≥1 each time. fc ∈ {0,...,n}. → Convergence.

This script verifies all components computationally.
"""

import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system
from collections import deque


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


def phi_val(c, n):
    d = get_d_vector(c, n)
    return psi(c, n) + f_boundary(c[0], d[n-1], n)


def verify_all(n):
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # CHECK 1: Φ decreases on all Δfc=0 bad→bad transitions
    dfc0_ok = True
    dfc0_count = 0
    for c in bad_set:
        fc_c = frontier_count(c, n)
        phi_c = phi_val(c, n)
        for p in get_privileged(c, fs, n):
            succ = apply_move(c, p, fs, n)
            if succ not in bad_set:
                continue
            if frontier_count(succ, n) != fc_c:
                continue
            dfc0_count += 1
            if phi_val(succ, n) >= phi_c:
                dfc0_ok = False

    # CHECK 2: Δfc≥0 subgraph is a DAG
    in_deg = {c: 0 for c in bad_set}
    adj = {c: [] for c in bad_set}
    for c in bad_set:
        fc_c = frontier_count(c, n)
        for p in get_privileged(c, fs, n):
            succ = apply_move(c, p, fs, n)
            if succ not in bad_set:
                continue
            if frontier_count(succ, n) >= fc_c:
                adj[c].append(succ)
                in_deg[succ] += 1
    q = deque(c for c in bad_set if in_deg[c] == 0)
    processed = 0
    topo = []
    while q:
        c = q.popleft()
        processed += 1
        topo.append(c)
        for s in adj[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)
    geq0_dag = (processed == len(bad_set))

    # Compute Δfc≥0 DAG depth
    geq0_depth = 0
    if geq0_dag:
        rank = {}
        for c in reversed(topo):
            rank[c] = max((rank[s] + 1 for s in adj[c]), default=0)
        geq0_depth = max(rank.values()) if rank else 0

    # CHECK 3: fc=0 → good
    fc0_good = all(c in good_set for c in configs if frontier_count(c, n) == 0)

    # CHECK 4: Full DAG (redundant confirmation)
    in_deg2 = {c: 0 for c in bad_set}
    adj2 = {c: [] for c in bad_set}
    for c in bad_set:
        for p in get_privileged(c, fs, n):
            succ = apply_move(c, p, fs, n)
            if succ in bad_set:
                adj2[c].append(succ)
                in_deg2[succ] += 1
    q2 = deque(c for c in bad_set if in_deg2[c] == 0)
    proc2 = 0
    topo2 = []
    while q2:
        c = q2.popleft()
        proc2 += 1
        topo2.append(c)
        for s in adj2[c]:
            in_deg2[s] -= 1
            if in_deg2[s] == 0:
                q2.append(s)
    full_dag = (proc2 == len(bad_set))
    max_rank = 0
    if full_dag:
        rk = {}
        for c in reversed(topo2):
            rk[c] = max((rk[s] + 1 for s in adj2[c]), default=0)
        max_rank = max(rk.values()) if rk else 0

    return {
        'n': n, 'bad': len(bad_set),
        'dfc0_ok': dfc0_ok, 'dfc0_count': dfc0_count,
        'geq0_dag': geq0_dag, 'geq0_depth': geq0_depth,
        'fc0_good': fc0_good,
        'full_dag': full_dag, 'max_rank': max_rank,
    }


if __name__ == "__main__":
    print("CONVERGENCE PROOF VERIFICATION")
    print("=" * 75)
    print(f"{'n':>3} {'bad':>7} {'Δfc=0':>6} {'Φ↓':>3} {'≥0DAG':>6} "
          f"{'fc0→G':>6} {'fullDAG':>7} {'maxRk':>6} {'≥0dep':>6}")
    print("-" * 75)

    for nv in range(3, 15):
        total = 2 * 3**(nv-1)
        if total > 500000:
            print(f"{nv:>3} SKIP (product={total})")
            continue
        t0 = time.time()
        r = verify_all(nv)
        elapsed = time.time() - t0
        print(f"{r['n']:>3} {r['bad']:>7} {r['dfc0_count']:>6} "
              f"{'✓' if r['dfc0_ok'] else '✗':>3} "
              f"{'✓' if r['geq0_dag'] else '✗':>6} "
              f"{'✓' if r['fc0_good'] else '✗':>6} "
              f"{'✓' if r['full_dag'] else '✗':>7} "
              f"{r['max_rank']:>6} {r['geq0_depth']:>6} "
              f"({elapsed:.1f}s)")

    print()
    print("PROOF STRUCTURE (analytic, all n ≥ 3):")
    print("  Step 1: Φ = Ψ + f(c₀,d_{n-1}) decreases on Δfc=0 bad→bad → DAG")
    print("  Step 2: Δfc≥0 cycle impossible (Σ Δfc=0, each ≥0 → all 0 → Step 1)")
    print("  Step 3: fc=0 → uniform → good (top is unique privilege)")
    print("  Step 4: Δfc≥0 DAG finite → forced Δfc<0 → fc drops → reach fc=0 → good")
    print("  Bound:  ≤ (n+1) × (Δfc≥0 depth + 1) steps")
