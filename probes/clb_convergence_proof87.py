#!/usr/bin/env python3
"""
CONVERGENCE PROOF 87: Δfc subgraph analysis within triple-preserved
====================================================================
Key question: what is the rank of the Δfc≥0 subgraph of TP?
If bounded by K, can define Φ = (K+1)·(fc_max - fc) - rank_up_in_Δfc≥0.

Also: check the Δfc=0 subgraph structure.
And: try decomposing TP = Δfc<0 ∪ Δfc=0 ∪ Δfc>0 and analyzing each part.
"""
import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter, deque


def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def int_20(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def exp2_count(c, n):
    return int_20(c, n) + int_21(c, n)

def intj_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def intj_21(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def exp2_weight(c, n):
    return intj_20(c, n) + intj_21(c, n)

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def dag_rank(adj, nodes):
    """Compute DAG rank (max path length from each node) via reverse BFS."""
    out_deg = defaultdict(int)
    radj = defaultdict(list)
    for c in nodes:
        out_deg[c] = len(adj.get(c, []))
        for s in adj.get(c, []):
            radj[s].append(c)

    sinks = [c for c in nodes if out_deg[c] == 0]
    rank = {c: 0 for c in sinks}
    q = deque(sinks)
    processed = len(sinks)
    while q:
        c = q.popleft()
        for p in radj[c]:
            new_r = rank[c] + 1
            if p not in rank or new_r > rank[p]:
                rank[p] = new_r
                if p not in rank:
                    processed += 1
                q.append(p)

    # Check if DAG (all nodes reached)
    is_dag = len(rank) == len(nodes)
    max_r = max(rank.values()) if rank else 0
    return rank, max_r, is_dag


def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 12):
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        # Build TP subgraph with Δfc annotation
        tp_adj_all = defaultdict(list)  # all TP edges
        tp_adj_pos = defaultdict(list)  # Δfc > 0
        tp_adj_zer = defaultdict(list)  # Δfc = 0
        tp_adj_neg = defaultdict(list)  # Δfc < 0
        tp_adj_ge0 = defaultdict(list)  # Δfc >= 0
        tp_adj_le0 = defaultdict(list)  # Δfc <= 0
        tp_nodes = set()
        dfc_dist = Counter()

        for c in bad_list:
            e2c = exp2_count(c, n)
            i21c = int_21(c, n)
            ewc = exp2_weight(c, n)
            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                out = fs[i](L, S, R)
                if out != S:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        e2s = exp2_count(succ, n)
                        i21s = int_21(succ, n)
                        ews = exp2_weight(succ, n)
                        if e2s == e2c and i21s == i21c and ews == ewc:
                            dfc_val = fc(succ, n) - fc(c, n)
                            dfc_dist[dfc_val] += 1
                            tp_adj_all[c].append(succ)
                            tp_nodes.add(c)
                            tp_nodes.add(succ)
                            if dfc_val > 0:
                                tp_adj_pos[c].append(succ)
                            elif dfc_val == 0:
                                tp_adj_zer[c].append(succ)
                            else:
                                tp_adj_neg[c].append(succ)
                            if dfc_val >= 0:
                                tp_adj_ge0[c].append(succ)
                            if dfc_val <= 0:
                                tp_adj_le0[c].append(succ)

        # Add isolated bad configs as nodes
        for c in bad_list:
            tp_nodes.add(c)

        elapsed = time.time() - t0
        n_edges = sum(dfc_dist.values())
        print(f"\n{'='*70}")
        print(f"n={n}: {n_edges} TP edges, {len(tp_nodes)} nodes ({elapsed:.1f}s)")
        print(f"  Δfc distribution: {dict(sorted(dfc_dist.items()))}")

        # Compute ranks for various subgraphs
        _, r_all, dag_all = dag_rank(tp_adj_all, tp_nodes)
        _, r_pos, dag_pos = dag_rank(tp_adj_pos, tp_nodes)
        _, r_zer, dag_zer = dag_rank(tp_adj_zer, tp_nodes)
        _, r_neg, dag_neg = dag_rank(tp_adj_neg, tp_nodes)
        _, r_ge0, dag_ge0 = dag_rank(tp_adj_ge0, tp_nodes)
        _, r_le0, dag_le0 = dag_rank(tp_adj_le0, tp_nodes)

        print(f"\n  Subgraph DAG analysis:")
        print(f"    Full TP:      DAG={'Y' if dag_all else 'N':1s}  rank={r_all}")
        print(f"    Δfc > 0:      DAG={'Y' if dag_pos else 'N':1s}  rank={r_pos}")
        print(f"    Δfc = 0:      DAG={'Y' if dag_zer else 'N':1s}  rank={r_zer}")
        print(f"    Δfc < 0:      DAG={'Y' if dag_neg else 'N':1s}  rank={r_neg}")
        print(f"    Δfc >= 0:     DAG={'Y' if dag_ge0 else 'N':1s}  rank={r_ge0}")
        print(f"    Δfc <= 0:     DAG={'Y' if dag_le0 else 'N':1s}  rank={r_le0}")

        # KEY: if Δfc≥0 rank is bounded by K, test the combined potential
        if dag_ge0 and dag_le0:
            rank_ge0, _, _ = dag_rank(tp_adj_ge0, tp_nodes)
            rank_le0, _, _ = dag_rank(tp_adj_le0, tp_nodes)
            K = r_ge0

            # Test potential: Φ = (K+1) * rank_le0 - rank_ge0
            # On Δfc≤0 edge: rank_le0 decreases by ≥1, rank_ge0 change ≤ K
            #   ΔΦ = (K+1)·Δr_le0 - Δr_ge0 ≤ -(K+1) + K = -1 ✓
            # On Δfc≥0 edge: rank_ge0 decreases by ≥1, rank_le0 change ≤ r_le0
            #   ΔΦ = (K+1)·Δr_le0 - Δr_ge0.
            #   rank_le0 can INCREASE by up to r_le0 on Δfc>0 edges...
            # Actually, does rank_le0 even decrease on Δfc≤0 edges?
            # Only if the edge IS in the Δfc≤0 subgraph, which it is.

            # Better: test Φ = (K+1) * rank_le0 + (K - rank_ge0)
            # = (K+1) * rank_le0 + K - rank_ge0
            # On Δfc≤0 edge (in le0 DAG):
            #   Δ(rank_le0) ≤ -1. Δ(rank_ge0) can be anything.
            #   ΔΦ = (K+1)·Δr_le0 - Δr_ge0 ≤ (K+1)(-1) + K = -1 ✓
            #   IF Δr_ge0 ≤ K on Δfc≤0 edges.
            #   rank_ge0 ∈ [0, K], so Δr_ge0 ≤ K - 0 = K. ✓

            # On Δfc>0 edge (in ge0 DAG):
            #   Δ(rank_ge0) ≤ -1. Δ(rank_le0) can increase.
            #   ΔΦ = (K+1)·Δr_le0 - Δr_ge0
            #   Need: (K+1)·Δr_le0 ≤ Δr_ge0 - 1
            #   i.e., (K+1)·Δr_le0 ≤ -2  (since Δr_ge0 ≤ -1)
            #   This needs Δr_le0 < 0, which is NOT guaranteed on Δfc>0 edges!

            # So the simple combination DOESN'T work.
            # Let me just TEST it computationally.

            violations = 0
            for c in tp_nodes:
                phi_c = (K + 1) * rank_le0.get(c, 0) + (K - rank_ge0.get(c, 0))
                for s in tp_adj_all.get(c, []):
                    phi_s = (K + 1) * rank_le0.get(s, 0) + (K - rank_ge0.get(s, 0))
                    if phi_s >= phi_c:
                        violations += 1

            print(f"\n  Combined potential Φ=(K+1)·r_le0+(K-r_ge0) where K={K}:")
            print(f"    Violations: {violations}/{n_edges}")

            # Alternative: just test Φ = r_le0·M - r_ge0 for various M
            for M in [1, 2, 5, 10, 50, r_le0 + 1]:
                viol = 0
                for c in tp_nodes:
                    phi_c = M * rank_le0.get(c, 0) - rank_ge0.get(c, 0)
                    for s in tp_adj_all.get(c, []):
                        phi_s = M * rank_le0.get(s, 0) - rank_ge0.get(s, 0)
                        if phi_s >= phi_c:
                            viol += 1
                if viol == 0:
                    print(f"    M={M}: Φ=M·r_le0 - r_ge0: ZERO violations! ✓")
                    break
                else:
                    print(f"    M={M}: Φ=M·r_le0 - r_ge0: {viol} violations")

            # What about Φ = rank_le0 alone? (ignoring ge0)
            viol_le0 = sum(1 for c in tp_nodes
                          for s in tp_adj_all.get(c, [])
                          if rank_le0.get(s, 0) >= rank_le0.get(c, 0))
            print(f"    r_le0 alone: {viol_le0} violations (Δfc>0 edges)")

            # What about r_ge0 alone?
            viol_ge0 = sum(1 for c in tp_nodes
                          for s in tp_adj_all.get(c, [])
                          if rank_ge0.get(s, 0) >= rank_ge0.get(c, 0))
            print(f"    r_ge0 alone: {viol_ge0} violations (Δfc<0 edges)")

            # Can we bound Δ(rank_le0) on Δfc>0 edges?
            if tp_adj_pos:
                drl_on_pos = []
                for c in tp_nodes:
                    for s in tp_adj_pos.get(c, []):
                        dr = rank_le0.get(s, 0) - rank_le0.get(c, 0)
                        drl_on_pos.append(dr)
                if drl_on_pos:
                    print(f"\n  Δ(rank_le0) on Δfc>0 edges: "
                          f"min={min(drl_on_pos)}, max={max(drl_on_pos)}")
                    print(f"    Distribution: {Counter(drl_on_pos).most_common(10)}")

            # Similarly, Δ(rank_ge0) on Δfc<0 edges
            if tp_adj_neg:
                drg_on_neg = []
                for c in tp_nodes:
                    for s in tp_adj_neg.get(c, []):
                        dr = rank_ge0.get(s, 0) - rank_ge0.get(c, 0)
                        drg_on_neg.append(dr)
                if drg_on_neg:
                    print(f"  Δ(rank_ge0) on Δfc<0 edges: "
                          f"min={min(drg_on_neg)}, max={max(drg_on_neg)}")
                    print(f"    Distribution: {Counter(drg_on_neg).most_common(10)}")

        print(f"  Time: {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
