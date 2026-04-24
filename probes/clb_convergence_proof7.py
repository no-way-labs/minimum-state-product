#!/usr/bin/env python3
"""Convergence proof investigation — Part 7.

APPROACH: Decompose the actual DAG rank function.
1. Can rank be expressed as sum of local contributions?
2. Is there a recursive structure?
3. What about rank modulo some value?
4. Direct induction proof: does removing the center processor
   relate n-system ranks to (n-1)-system ranks?
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import deque, defaultdict, Counter
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system


def get_bad_graph_with_ranks(n):
    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(c for c in all_configs if c not in good_set)

    adj = {c: [] for c in bad_set}
    in_deg = {c: 0 for c in bad_set}
    for c in bad_set:
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    adj[c].append((succ, i))
                    in_deg[succ] += 1

    q = deque(c for c in bad_set if in_deg[c] == 0)
    topo = []
    while q:
        c = q.popleft()
        topo.append(c)
        for succ, _ in adj[c]:
            in_deg[succ] -= 1
            if in_deg[succ] == 0:
                q.append(succ)

    rank = {}
    for c in reversed(topo):
        succs = [s for s, _ in adj[c]]
        rank[c] = max((rank[s] + 1 for s in succs), default=0)

    return ms, fs, good_set, bad_set, adj, rank


def main():
    # ================================================================
    # PART 1: RANK DECOMPOSITION — IS RANK A SUM OF LOCAL TERMS?
    # ================================================================
    print("=" * 90)
    print("PART 1: RANK DECOMPOSITION")
    print("=" * 90)

    for nv in [6, 7]:
        ms, fs, good_set, bad_set, adj, rank = get_bad_graph_with_ranks(nv)
        n = nv

        # Can we write rank(c) ≈ Σ_i w_i(c[i-1], c[i], c[i+1])?
        # This is a "sum of local contributions" model.
        # Fit: find w_i for each position's local triples.

        # For each position and each (L,S,R) triple, collect all rank values
        # of configs with that triple at position i.
        # If rank ≈ Σ w_i(L,S,R), then the average rank for a specific
        # (L,S,R) at position i should be close to the overall average
        # plus w_i(L,S,R).

        configs = list(bad_set)
        avg_rank = sum(rank[c] for c in configs) / len(configs)

        print(f"\nn={nv}: {len(configs)} configs, avg_rank={avg_rank:.2f}, "
              f"max_rank={max(rank.values())}")

        # For each position, compute the "rank contribution" for each (L,S,R)
        for pos in [0, 1, n//2, n-2, n-1]:
            print(f"\n  Position P{pos}:")
            triple_ranks = defaultdict(list)
            for c in configs:
                L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]
                triple_ranks[(L, S, R)].append(rank[c])

            for triple in sorted(triple_ranks.keys()):
                ranks_list = triple_ranks[triple]
                if len(ranks_list) < 2:
                    continue
                avg = sum(ranks_list) / len(ranks_list)
                std = (sum((r - avg)**2 for r in ranks_list) / len(ranks_list)) ** 0.5
                contrib = avg - avg_rank
                print(f"    ({triple[0]},{triple[1]},{triple[2]}): "
                      f"avg_rank={avg:.1f} (contrib={contrib:+.1f}), "
                      f"std={std:.1f}, n={len(ranks_list)}")

    # ================================================================
    # PART 2: RANK RESIDUALS — WHAT'S LEFT AFTER SUBTRACTING PRIV/SUM?
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 2: RANK RESIDUALS")
    print("=" * 90)

    for nv in [6, 7, 8]:
        ms, fs, good_set, bad_set, adj, rank = get_bad_graph_with_ranks(nv)
        n = nv
        configs = list(bad_set)

        # Compute features
        def n_priv(c):
            return sum(1 for i in range(n)
                       if fs[i](c[(i-1)%n], c[i], c[(i+1)%n]) != c[i])

        def total_sum(c):
            return sum(c)

        # Linear model: rank ≈ a * n_priv + b * sum + c_const
        # Least squares (using numpy-free approach)
        x_data = [(n_priv(c), total_sum(c), 1) for c in configs]
        y_data = [rank[c] for c in configs]

        # Simple 3x3 solve (or just try a,b from grid)
        best_resid = float('inf')
        best_params = None
        for a in [i * 0.5 for i in range(-10, 11)]:
            for b in [i * 0.5 for i in range(-10, 11)]:
                for const in [i for i in range(-20, 21)]:
                    resid = sum((rank[c] - a * n_priv(c) - b * total_sum(c) - const)**2
                               for c in configs)
                    if resid < best_resid:
                        best_resid = resid
                        best_params = (a, b, const)

        a, b, const = best_params
        rmse = (best_resid / len(configs)) ** 0.5
        print(f"\nn={nv}: rank ≈ {a}*n_priv + {b}*sum + {const}")
        print(f"  RMSE = {rmse:.2f}, max|residual| = "
              f"{max(abs(rank[c] - a*n_priv(c) - b*total_sum(c) - const) for c in configs):.1f}")

        # What do the residuals look like?
        residuals = sorted([(rank[c] - a*n_priv(c) - b*total_sum(c) - const, c)
                           for c in configs])
        print(f"  Largest negative residuals (rank << prediction):")
        for r, c in residuals[:5]:
            print(f"    {c}: rank={rank[c]}, predicted={rank[c]-r:.1f}, resid={r:.1f}")
        print(f"  Largest positive residuals (rank >> prediction):")
        for r, c in residuals[-5:]:
            print(f"    {c}: rank={rank[c]}, predicted={rank[c]-r:.1f}, resid={r:.1f}")

    # ================================================================
    # PART 3: PROJECTION FROM n TO n-1
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 3: INDUCTIVE STRUCTURE — PROJECTION n → n-1")
    print("=" * 90)

    # If we remove the center position and "compress" the ring,
    # does the rank relate to the (n-1)-system rank?

    for nv in [7, 8, 9]:
        ms_n, fs_n, good_n, bad_n, adj_n, rank_n = get_bad_graph_with_ranks(nv)
        ms_m, fs_m, good_m, bad_m, adj_m, rank_m = get_bad_graph_with_ranks(nv - 1)
        n = nv
        center = n // 2

        # Project: remove position 'center' from each config
        def project(c, pos):
            return c[:pos] + c[pos+1:]

        # For each n-config, project to (n-1)-config
        proj_ranks = []
        matches = 0
        mismatches = 0
        for c in bad_n:
            p = project(c, center)
            if p in bad_m:
                proj_ranks.append((rank_n[c], rank_m[p], c[center]))
                matches += 1
            else:
                mismatches += 1

        print(f"\nn={nv}→{nv-1} (remove P{center}): "
              f"{matches} project to bad, {mismatches} project to good")

        if proj_ranks:
            # Group by c[center]
            for v in range(3):
                data = [(rn, rm) for rn, rm, cv in proj_ranks if cv == v]
                if not data:
                    continue
                # Compute correlation
                avg_rn = sum(rn for rn, _ in data) / len(data)
                avg_rm = sum(rm for _, rm in data) / len(data)
                cov = sum((rn - avg_rn) * (rm - avg_rm) for rn, rm in data) / len(data)
                var_rn = sum((rn - avg_rn)**2 for rn, _ in data) / len(data)
                var_rm = sum((rm - avg_rm)**2 for _, rm in data) / len(data)
                corr = cov / (var_rn * var_rm) ** 0.5 if var_rn > 0 and var_rm > 0 else 0
                print(f"  c[{center}]={v}: {len(data)} pairs, "
                      f"corr(rank_n, rank_{nv-1})={corr:.4f}")

    # ================================================================
    # PART 4: THE CRITICAL TEST — ARE THERE "TRAPPED" CONFIGS?
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 4: CONFIGS WITH ALL BAD SUCCESSORS (no escape)")
    print("=" * 90)

    # A "trapped" config has ALL transitions leading to other bad configs.
    # If there are NO trapped configs (every config has at least one escape to good),
    # that's a strong property of the good-targeting construction.

    for nv in range(5, 13):
        ms, fs, good_set, bad_set, adj, rank = get_bad_graph_with_ranks(nv)
        n = nv

        trapped = 0
        has_escape = 0
        for c in bad_set:
            all_bad = True
            for i in range(n):
                L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c); lst[i] = new_S; succ = tuple(lst)
                    if succ not in bad_set:
                        all_bad = False
                        break
            if all_bad:
                trapped += 1
            else:
                has_escape += 1

        pct_trapped = 100 * trapped / len(bad_set)
        print(f"  n={nv}: {trapped}/{len(bad_set)} trapped ({pct_trapped:.1f}%), "
              f"{has_escape} have escape")

        if trapped > 0 and nv <= 8:
            # Show a few trapped configs and their ranks
            trapped_configs = [c for c in bad_set
                              if all(tuple(list(c)[:i] + [fs[i](c[(i-1)%n], c[i], c[(i+1)%n])]
                                     + list(c)[i+1:]) in bad_set
                                     for i in range(n)
                                     if fs[i](c[(i-1)%n], c[i], c[(i+1)%n]) != c[i])]
            for c in sorted(trapped_configs, key=lambda c: -rank[c])[:5]:
                print(f"    {c}: rank={rank[c]}")

        if 4 * 3 ** (nv - 2) > 500000:
            break

    # ================================================================
    # PART 5: THE "k-STEP ESCAPE" PROPERTY
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 5: k-STEP ESCAPE — SHORTEST PATH TO GOOD")
    print("=" * 90)

    for nv in [6, 7, 8]:
        ms, fs, good_set, bad_set, adj, rank = get_bad_graph_with_ranks(nv)
        n = nv

        # BFS from good set backward
        all_configs = set(cartesian(*(range(m) for m in ms)))
        rev_adj = defaultdict(list)
        for c in bad_set:
            for succ, mover in adj[c]:
                rev_adj[succ].append(c)

        dist = {}
        queue = deque()

        # Distance to good: forward BFS from each bad config
        # Actually, reverse BFS from good configs
        for c in bad_set:
            for i in range(n):
                L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c); lst[i] = new_S; succ = tuple(lst)
                    if succ in good_set:
                        if c not in dist:
                            dist[c] = 1
                            queue.append(c)

        while queue:
            c = queue.popleft()
            d = dist[c]
            for pred in rev_adj.get(c, []):
                if pred not in dist:
                    dist[pred] = d + 1
                    queue.append(pred)

        if dist:
            max_dist = max(dist.values())
            # Distribution
            dist_counts = Counter(dist.values())
            print(f"\nn={nv}: shortest path to good distribution:")
            print(f"  max_dist={max_dist}, all reached={len(dist)==len(bad_set)}")
            for d in sorted(dist_counts.keys()):
                print(f"    dist={d}: {dist_counts[d]} configs")

            # Correlation between shortest distance and rank
            both = [(dist[c], rank[c]) for c in bad_set if c in dist]
            if both:
                avg_d = sum(d for d, _ in both) / len(both)
                avg_r = sum(r for _, r in both) / len(both)
                cov = sum((d-avg_d)*(r-avg_r) for d, r in both) / len(both)
                var_d = sum((d-avg_d)**2 for d, _ in both) / len(both)
                var_r = sum((r-avg_r)**2 for _, r in both) / len(both)
                corr = cov / (var_d * var_r)**0.5 if var_d > 0 and var_r > 0 else 0
                print(f"  Correlation(shortest_dist, DAG_rank) = {corr:.4f}")

    # ================================================================
    # PART 6: EVERY TRANSITION EITHER ESCAPES OR SHORTENS PATH
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 6: DOES EVERY TRANSITION SHORTEN OR MAINTAIN SHORTEST PATH?")
    print("=" * 90)

    for nv in [6, 7, 8]:
        ms, fs, good_set, bad_set, adj, rank = get_bad_graph_with_ranks(nv)
        n = nv

        # Compute shortest dist to good
        dist = {}
        queue = deque()
        rev_adj = defaultdict(list)
        for c in bad_set:
            for succ, mover in adj[c]:
                rev_adj[succ].append(c)
            for i in range(n):
                L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c); lst[i] = new_S; succ = tuple(lst)
                    if succ in good_set:
                        if c not in dist:
                            dist[c] = 1
                            queue.append(c)

        while queue:
            c = queue.popleft()
            d = dist[c]
            for pred in rev_adj.get(c, []):
                if pred not in dist:
                    dist[pred] = d + 1
                    queue.append(pred)

        # For each bad→bad transition c → c', compare dist
        increases = 0
        decreases = 0
        same = 0
        total = 0
        for c in bad_set:
            for succ, mover in adj[c]:
                total += 1
                dc = dist.get(c, float('inf'))
                dcp = dist.get(succ, float('inf'))
                if dcp > dc:
                    increases += 1
                elif dcp < dc:
                    decreases += 1
                else:
                    same += 1

        print(f"  n={nv}: shortest_dist changes: ↑={increases} (farther from good), "
              f"=={same}, ↓={decreases} (closer)")
        print(f"    increases/{total} = {100*increases/total:.1f}%")

    # ================================================================
    # PART 7: THE "GOOD NEIGHBOR" PROPERTY
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 7: GOOD NEIGHBOR — DOES EVERY CONFIG HAVE A GOOD-ADJACENT TRANSITION?")
    print("=" * 90)

    for nv in range(5, 13):
        ms, fs, good_set, bad_set, adj, rank = get_bad_graph_with_ranks(nv)
        n = nv

        # "Good-adjacent": exists a transition c → c' where c' is good
        # OR c' has a transition to good (2-step escape)
        # This is dist(c) ≤ 2.

        # Already computed dist for some n, but let me be more efficient
        dist1_count = 0
        dist2_count = 0

        for c in bad_set:
            best_step = float('inf')
            for i in range(n):
                L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c); lst[i] = new_S; succ = tuple(lst)
                    if succ in good_set:
                        best_step = 1
                        break
                    elif succ in bad_set:
                        # Check if succ has a 1-step escape
                        for j in range(n):
                            L2 = succ[(j-1)%n]; S2 = succ[j]; R2 = succ[(j+1)%n]
                            new_S2 = fs[j](L2, S2, R2)
                            if new_S2 != S2:
                                lst2 = list(succ); lst2[j] = new_S2; s2 = tuple(lst2)
                                if s2 in good_set:
                                    best_step = min(best_step, 2)
                                    break

            if best_step == 1:
                dist1_count += 1
            elif best_step == 2:
                dist2_count += 1

        pct1 = 100 * dist1_count / len(bad_set)
        pct2 = 100 * (dist1_count + dist2_count) / len(bad_set)
        print(f"  n={nv}: 1-step escape={dist1_count} ({pct1:.1f}%), "
              f"≤2-step={dist1_count+dist2_count} ({pct2:.1f}%)")

        if 4 * 3 ** (nv - 2) > 200000:
            break

    # ================================================================
    # PART 8: KEY STRUCTURAL INSIGHT — RANK BY PRIVILEGE SET SIZE
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 8: RANK BY (PRIV_COUNT, TRANSITION TYPE)")
    print("=" * 90)

    for nv in [6, 7]:
        ms, fs, good_set, bad_set, adj, rank = get_bad_graph_with_ranks(nv)
        n = nv

        # For each bad→bad transition, does RANK always decrease?
        # We know it does (DAG property). But what's the STEP in rank?
        rank_steps = defaultdict(list)

        for c in bad_set:
            for succ, mover in adj[c]:
                step = rank[c] - rank[succ]
                priv_c = sum(1 for i in range(n)
                            if fs[i](c[(i-1)%n], c[i], c[(i+1)%n]) != c[i])

                tbl = 'bot' if mover == 0 else 'low' if mover == 1 else \
                      'mid' if mover < n-2 else 'high' if mover == n-2 else 'top'
                old_v = c[mover]
                new_v = succ[mover]
                key = (tbl, old_v, new_v, priv_c)
                rank_steps[key].append(step)

        print(f"\nn={nv}: Average rank step by transition type and priv count:")
        print(f"  {'table':>5} {'chg':>4} {'priv':>4} {'avg_step':>9} {'min':>4} {'max':>4} {'count':>5}")
        for key in sorted(rank_steps.keys()):
            tbl, old_v, new_v, priv = key
            steps = rank_steps[key]
            avg = sum(steps) / len(steps)
            if len(steps) >= 3:
                print(f"  {tbl:>5} {old_v}→{new_v}  {priv:>4} {avg:>9.2f} "
                      f"{min(steps):>4} {max(steps):>4} {len(steps):>5}")


if __name__ == "__main__":
    main()
