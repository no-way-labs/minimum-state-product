#!/usr/bin/env python3
"""
CONVERGENCE PROOF 17: n=9 collision analysis
=============================================

The frozen-rank tuple determines DAG rank for n=5..8 but FAILS at n=9.
Analyze the collisions to understand what additional information is needed.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque, Counter, defaultdict


def compute_frozen_ranks(bad_list, bad_set, fs, ms, n):
    all_ranks = {}
    for p in range(n):
        adj = {c: [] for c in bad_list}
        for c in bad_list:
            for i in range(n):
                if i == p:
                    continue
                L = c[(i - 1) % n]
                S = c[i]
                R = c[(i + 1) % n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c)
                    lst[i] = new_S
                    succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append(succ)
        in_deg = {c: 0 for c in bad_list}
        for c in bad_list:
            for s in adj[c]:
                in_deg[s] += 1
        q = deque(c for c in bad_list if in_deg[c] == 0)
        topo = []
        while q:
            c = q.popleft()
            topo.append(c)
            for s in adj[c]:
                in_deg[s] -= 1
                if in_deg[s] == 0:
                    q.append(s)
        assert len(topo) == len(bad_list)
        rank = {}
        for c in reversed(topo):
            rank[c] = max((rank[s] + 1 for s in adj[c]), default=0)
        all_ranks[p] = rank
    return all_ranks


def analyze_collisions(n_val):
    ms, fs = build_system(n_val)
    n = n_val
    result = verify_system(ms, fs)
    assert result['valid']

    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    print(f"\n{'=' * 70}")
    print(f"n = {n_val}: {len(bad_list)} bad configs")
    print(f"{'=' * 70}")

    frozen = compute_frozen_ranks(bad_list, bad_set, fs, ms, n)

    # Build DAG and compute ranks
    transitions = []
    adj = {c: [] for c in bad_list}
    for c in bad_list:
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c)
                lst[i] = new_S
                succ = tuple(lst)
                if succ in bad_set:
                    adj[c].append(succ)
                    transitions.append((c, succ, i))

    in_deg = {c: 0 for c in bad_list}
    for c in bad_list:
        for s in adj[c]:
            in_deg[s] += 1
    q = deque(c for c in bad_list if in_deg[c] == 0)
    topo = []
    while q:
        c = q.popleft()
        topo.append(c)
        for s in adj[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)
    dag_rank = {}
    for c in reversed(topo):
        dag_rank[c] = max((dag_rank[s] + 1 for s in adj[c]), default=0)

    # Find collisions
    fr_tuple = {}
    for c in bad_list:
        fr_tuple[c] = tuple(frozen[p][c] for p in range(n))

    tuple_to_configs = defaultdict(list)
    for c in bad_list:
        tuple_to_configs[fr_tuple[c]].append(c)

    collisions = {t: cs for t, cs in tuple_to_configs.items()
                  if len(set(dag_rank[c] for c in cs)) > 1}

    print(f"  Unique tuples: {len(tuple_to_configs)}")
    print(f"  Tuples with DAG rank collision: {len(collisions)}")

    if not collisions:
        print("  No collisions — determinism holds!")
        return

    # Analyze each collision
    for t, cs in sorted(collisions.items(),
                        key=lambda x: max(dag_rank[c] for c in x[1]),
                        reverse=True)[:20]:
        ranks = sorted(set(dag_rank[c] for c in cs), reverse=True)
        print(f"\n  Tuple: {t}")
        print(f"    DAG ranks: {ranks}")
        for rank_val in ranks:
            rank_configs = [c for c in cs if dag_rank[c] == rank_val]
            for c in rank_configs[:3]:
                # Show config and its local properties
                priv = [i for i in range(n)
                        if fs[i](c[(i-1)%n], c[i], c[(i+1)%n]) != c[i]]
                print(f"    R={rank_val}: c={c}, priv={priv}")
                # What position differ between configs at different ranks?

        # What positions differ between configs at different ranks?
        if len(ranks) == 2:
            r1, r2 = ranks
            cs1 = [c for c in cs if dag_rank[c] == r1]
            cs2 = [c for c in cs if dag_rank[c] == r2]
            # Find differing positions
            for c1 in cs1[:2]:
                for c2 in cs2[:2]:
                    diffs = [j for j in range(n) if c1[j] != c2[j]]
                    print(f"    Diff positions between R={r1} {c1} and R={r2} {c2}: {diffs}")
                    for j in diffs:
                        print(f"      pos {j}: {c1[j]} vs {c2[j]}, "
                              f"neighbors: L={c1[(j-1)%n]},{c2[(j-1)%n]} "
                              f"R={c1[(j+1)%n]},{c2[(j+1)%n]}")

    # ═══════════════════════════════════════════════════════════
    # What EXTRA information distinguishes collision configs?
    # ═══════════════════════════════════════════════════════════
    print(f"\n  EXTRA FEATURES to distinguish collisions:")

    # Feature 1: Number of privileged positions
    n_priv_resolves = 0
    for t, cs in collisions.items():
        priv_counts = {}
        for c in cs:
            np = len([i for i in range(n)
                     if fs[i](c[(i-1)%n], c[i], c[(i+1)%n]) != c[i]])
            priv_counts.setdefault(np, set()).add(dag_rank[c])
        if all(len(ranks) == 1 for ranks in priv_counts.values()):
            n_priv_resolves += 1
    print(f"  #privileged resolves: {n_priv_resolves}/{len(collisions)}")

    # Feature 2: Sum of values Σ c[i]
    n_sum_resolves = 0
    for t, cs in collisions.items():
        val_sums = {}
        for c in cs:
            s = sum(c)
            val_sums.setdefault(s, set()).add(dag_rank[c])
        if all(len(ranks) == 1 for ranks in val_sums.values()):
            n_sum_resolves += 1
    print(f"  Σc[i] resolves: {n_sum_resolves}/{len(collisions)}")

    # Feature 3: Boundary values (c[0], c[n-1])
    n_boundary_resolves = 0
    for t, cs in collisions.items():
        bvals = {}
        for c in cs:
            b = (c[0], c[n-1])
            bvals.setdefault(b, set()).add(dag_rank[c])
        if all(len(ranks) == 1 for ranks in bvals.values()):
            n_boundary_resolves += 1
    print(f"  Boundary (c[0],c[n-1]) resolves: {n_boundary_resolves}/{len(collisions)}")

    # Feature 4: "settled pattern" — which positions are at their target value
    n_settled_resolves = 0
    for t, cs in collisions.items():
        patterns = {}
        for c in cs:
            pat = tuple(1 if fs[i](c[(i-1)%n], c[i], c[(i+1)%n]) == c[i] else 0
                       for i in range(n))
            patterns.setdefault(pat, set()).add(dag_rank[c])
        if all(len(ranks) == 1 for ranks in patterns.values()):
            n_settled_resolves += 1
    print(f"  Settled pattern resolves: {n_settled_resolves}/{len(collisions)}")

    # Feature 5: Pair of adjacent values (c[i], c[i+1])
    n_pair_resolves = 0
    for t, cs in collisions.items():
        pairs = {}
        for c in cs:
            p = tuple((c[i], c[(i+1)%n]) for i in range(n))
            pairs.setdefault(p, set()).add(dag_rank[c])
        if all(len(ranks) == 1 for ranks in pairs.values()):
            n_pair_resolves += 1
    print(f"  Adjacent-pair signature resolves: {n_pair_resolves}/{len(collisions)}")

    # Feature 6: Frozen-rank tuple EXTENDED with one extra frozen-rank at pair level
    # For each pair (p,q), compute rank in {p,q}-frozen DAG
    # This is expensive, so try just a few pairs
    print(f"\n  Testing pair-frozen ranks to resolve collisions...")
    for p in range(n):
        for q in range(p + 1, min(p + 3, n)):
            # Build (p,q)-frozen DAG: exclude transitions at p AND q
            pq_adj = {c: [] for c in bad_list}
            for c in bad_list:
                for i in range(n):
                    if i == p or i == q:
                        continue
                    L = c[(i - 1) % n]
                    S = c[i]
                    R = c[(i + 1) % n]
                    new_S = fs[i](L, S, R)
                    if new_S != S:
                        lst = list(c)
                        lst[i] = new_S
                        succ = tuple(lst)
                        if succ in bad_set:
                            pq_adj[c].append(succ)

            pq_in = {c: 0 for c in bad_list}
            for c in bad_list:
                for s in pq_adj[c]:
                    pq_in[s] += 1
            pq_q = deque(c for c in bad_list if pq_in[c] == 0)
            pq_topo = []
            while pq_q:
                c = pq_q.popleft()
                pq_topo.append(c)
                for s in pq_adj[c]:
                    pq_in[s] -= 1
                    if pq_in[s] == 0:
                        pq_q.append(s)
            if len(pq_topo) != len(bad_list):
                print(f"    ({p},{q})-frozen: NOT a DAG!")
                continue
            pq_rank = {}
            for c in reversed(pq_topo):
                pq_rank[c] = max((pq_rank[s] + 1 for s in pq_adj[c]), default=0)

            # Check if adding pq_rank resolves collisions
            n_resolved = 0
            for t, cs in collisions.items():
                ext = {}
                for c in cs:
                    key = pq_rank[c]
                    ext.setdefault(key, set()).add(dag_rank[c])
                if all(len(ranks) == 1 for ranks in ext.values()):
                    n_resolved += 1
            if n_resolved > 0:
                print(f"    ({p},{q})-frozen rank resolves: {n_resolved}/{len(collisions)}")


if __name__ == '__main__':
    analyze_collisions(9)
