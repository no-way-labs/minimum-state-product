#!/usr/bin/env python3
"""
CONVERGENCE PROOF 84: Triple-preserved subgraph DAG analysis
=============================================================
The triple-preserved subgraph: all edges where
  Δ(int_20+int_21) = 0, Δint_21 = 0, Δ(intj_20+intj_21) = 0

From proof83: within this subgraph, NO T_mid entry with L=2 fires.
This means the interior "sees no 2 from the left" — strong constraint.

Check:
1. Is the triple-preserved subgraph a DAG?
2. If so, what's the max DAG depth?
3. What invariant works within it?
4. Compare with jdz excursion subgraph.
"""
import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque, defaultdict, Counter


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


def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 13):
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        # Build the triple-preserved subgraph
        tp_adj = defaultdict(list)
        tp_nodes = set()
        tp_edges = 0
        total_edges = 0

        # Also track full bad graph for comparison
        full_adj = defaultdict(list)

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
                        total_edges += 1
                        full_adj[c].append(succ)

                        e2s = exp2_count(succ, n)
                        i21s = int_21(succ, n)
                        ews = exp2_weight(succ, n)

                        if e2s == e2c and i21s == i21c and ews == ewc:
                            tp_adj[c].append(succ)
                            tp_nodes.add(c)
                            tp_nodes.add(succ)
                            tp_edges += 1

        # Check DAG property of triple-preserved subgraph
        in_deg = defaultdict(int)
        for c in tp_nodes:
            for s in tp_adj[c]:
                if s in tp_nodes:
                    in_deg[s] += 1

        q = deque(c for c in tp_nodes if in_deg[c] == 0)
        processed = 0
        topo = []
        while q:
            nd = q.popleft()
            processed += 1
            topo.append(nd)
            for s in tp_adj[nd]:
                if s in tp_nodes:
                    in_deg[s] -= 1
                    if in_deg[s] == 0:
                        q.append(s)

        is_dag = (processed == len(tp_nodes))

        # Compute DAG depth if it is a DAG
        max_depth = 0
        if is_dag:
            rank = {}
            for c in reversed(topo):
                r = 0
                for s in tp_adj[c]:
                    if s in tp_nodes and s in rank:
                        r = max(r, rank[s] + 1)
                rank[c] = r
            max_depth = max(rank.values()) if rank else 0

        elapsed = time.time() - t0

        print(f"\n{'='*70}")
        print(f"n={n}: {total_edges} total bad edges, "
              f"{tp_edges} triple-preserved ({100*tp_edges/total_edges:.1f}%)")
        print(f"  Triple-preserved nodes: {len(tp_nodes)} / {len(bad_list)} "
              f"({100*len(tp_nodes)/len(bad_list):.1f}%)")
        print(f"  DAG: {'YES' if is_dag else 'NO'}")
        if is_dag:
            print(f"  Max depth: {max_depth}")
        else:
            # Find cycle
            print(f"  Processed: {processed}/{len(tp_nodes)} (cycle exists!)")

        # Check fc distribution on triple-preserved edges
        dfc_dist = Counter()
        for c in tp_nodes:
            for s in tp_adj[c]:
                if s in tp_nodes:
                    dfc = fc(s, n) - fc(c, n)
                    dfc_dist[dfc] += 1
        print(f"  Δfc distribution: {dict(sorted(dfc_dist.items()))}")

        # How many edges have Δfc > 0?
        dfc_pos = sum(v for k, v in dfc_dist.items() if k > 0)
        dfc_zero = dfc_dist.get(0, 0)
        dfc_neg = sum(v for k, v in dfc_dist.items() if k < 0)
        print(f"  Δfc: neg={dfc_neg}, zero={dfc_zero}, pos={dfc_pos}")

        # Check if fc-non-increasing subgraph is DAG
        if is_dag and dfc_pos > 0:
            # Build fc-non-increasing sub of triple-preserved
            fni_adj = defaultdict(list)
            fni_nodes = set()
            for c in tp_nodes:
                for s in tp_adj[c]:
                    if s in tp_nodes and fc(s, n) <= fc(c, n):
                        fni_adj[c].append(s)
                        fni_nodes.add(c)
                        fni_nodes.add(s)

            fni_id = defaultdict(int)
            for c in fni_nodes:
                for s in fni_adj[c]:
                    if s in fni_nodes:
                        fni_id[s] += 1
            q2 = deque(c for c in fni_nodes if fni_id[c] == 0)
            proc2 = 0
            topo2 = []
            while q2:
                nd = q2.popleft()
                proc2 += 1
                topo2.append(nd)
                for s in fni_adj[nd]:
                    if s in fni_nodes:
                        fni_id[s] -= 1
                        if fni_id[s] == 0:
                            q2.append(s)
            fni_dag = (proc2 == len(fni_nodes))
            fni_depth = 0
            if fni_dag:
                fni_rank = {}
                for c in reversed(topo2):
                    r = 0
                    for s in fni_adj[c]:
                        if s in fni_nodes and s in fni_rank:
                            r = max(r, fni_rank[s] + 1)
                    fni_rank[c] = r
                fni_depth = max(fni_rank.values()) if fni_rank else 0
            print(f"  Δfc≤0 sub: DAG={'YES' if fni_dag else 'NO'}, "
                  f"depth={fni_depth}")

        # For the full bad graph: check DAG
        full_in = defaultdict(int)
        for c in bad_list:
            for s in full_adj[c]:
                full_in[s] += 1
        q3 = deque(c for c in bad_list if full_in[c] == 0)
        proc3 = 0
        while q3:
            nd = q3.popleft()
            proc3 += 1
            for s in full_adj[nd]:
                full_in[s] -= 1
                if full_in[s] == 0:
                    q3.append(s)
        full_dag = (proc3 == len(bad_list))
        print(f"  Full bad graph DAG: {'YES' if full_dag else 'NO'}")

        print(f"  Time: {elapsed:.1f}s")


if __name__ == '__main__':
    main()
