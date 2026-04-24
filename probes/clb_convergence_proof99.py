#!/usr/bin/env python3
"""
CONVERGENCE PROOF 99: The Φ = fc + g potential — DAG of ΔΦ≥0 subgraph
========================================================================
DISCOVERY: Φ = fc + g (where g = max future fc gain on Δfc≥0 TP paths)
has only ~1% violations, all of type ΔΦ = +1, at exactly TWO entries:
  - pos 1: T_low(0,1,2)→0, Δfc=-1, Δg=+2
  - pos n-1: T_top(1,0,1)→1, Δfc=-2, Δg=+3

PROOF STRATEGY: If the ΔΦ≥0 subgraph (constant + violation edges) is a DAG,
then the lexicographic pair (Φ, rank_in_ΔΦ≥0) is strictly decreasing on
ALL TP edges. This proves the TP subgraph is a DAG!

Why: On ΔΦ<0 edges, Φ decreases (first component drops).
     On ΔΦ≥0 edges, rank_in_ΔΦ≥0 decreases (since this subgraph is a DAG).
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

        if n >= 12 and len(bad_list) > 200000:
            print(f"\nn={n}: skipping (too large: {len(bad_list)} bad configs)")
            continue

        # Build TP edges
        tp_adj_ge0_fc = defaultdict(list)  # Δfc≥0 edges
        tp_edges = []
        tp_nodes = set()
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
                            dfc = fc(succ, n) - fc(c, n)
                            tp_edges.append((c, succ, i, dfc))
                            tp_nodes.add(c); tp_nodes.add(succ)
                            if dfc >= 0:
                                tp_adj_ge0_fc[c].append((succ, dfc, i))

        # Compute g = max future fc gain on Δfc≥0 paths
        # Reverse BFS from sinks
        tp_radj_ge0 = defaultdict(list)
        for c in tp_nodes:
            for s, dfc, pos in tp_adj_ge0_fc.get(c, []):
                tp_radj_ge0[s].append((c, dfc))

        g = {}
        for c in tp_nodes:
            if not tp_adj_ge0_fc.get(c):
                g[c] = 0
        q = deque(g.keys())
        while q:
            s = q.popleft()
            for c, dfc in tp_radj_ge0.get(s, []):
                new_g = dfc + g.get(s, 0)
                if c not in g or new_g > g[c]:
                    g[c] = new_g
                    q.append(c)

        # Compute Φ = fc + g for each config
        phi = {c: fc(c, n) + g.get(c, 0) for c in tp_nodes}

        # Classify TP edges by ΔΦ
        phi_ge0_edges = []  # ΔΦ ≥ 0
        phi_lt0_edges = []
        phi_gt0_cnt = 0
        phi_eq0_cnt = 0
        for c, s, pos, dfc in tp_edges:
            dphi = phi.get(s, 0) - phi.get(c, 0)
            if dphi >= 0:
                phi_ge0_edges.append((c, s, pos, dfc, dphi))
                if dphi > 0:
                    phi_gt0_cnt += 1
                else:
                    phi_eq0_cnt += 1
            else:
                phi_lt0_edges.append((c, s, pos, dfc, dphi))

        # Check if ΔΦ≥0 subgraph is a DAG (use DFS for cycle detection)
        phi_ge0_adj = defaultdict(list)
        phi_ge0_nodes = set()
        for c, s, pos, dfc, dphi in phi_ge0_edges:
            phi_ge0_adj[c].append(s)
            phi_ge0_nodes.add(c)
            phi_ge0_nodes.add(s)

        # Cycle detection via DFS
        WHITE, GRAY, BLACK = 0, 1, 2
        color = {c: WHITE for c in phi_ge0_nodes}
        has_cycle = False
        cycle_node = None

        def dfs_check():
            nonlocal has_cycle, cycle_node
            for start in phi_ge0_nodes:
                if color[start] != WHITE:
                    continue
                stack = [(start, False)]
                while stack:
                    node, returning = stack.pop()
                    if returning:
                        color[node] = BLACK
                        continue
                    if color[node] == GRAY:
                        continue
                    if color[node] == BLACK:
                        continue
                    color[node] = GRAY
                    stack.append((node, True))
                    for s in phi_ge0_adj.get(node, []):
                        if color[s] == GRAY:
                            has_cycle = True
                            cycle_node = s
                            return
                        if color[s] == WHITE:
                            stack.append((s, False))

        dfs_check()

        # Compute rank in ΔΦ≥0 subgraph
        phi_ge0_out = {c: len(phi_ge0_adj.get(c, [])) for c in phi_ge0_nodes}
        phi_ge0_sinks = [c for c in phi_ge0_nodes if phi_ge0_out[c] == 0]
        phi_ge0_rank = {c: 0 for c in phi_ge0_sinks}
        phi_ge0_radj = defaultdict(list)
        for c in phi_ge0_nodes:
            for s in phi_ge0_adj.get(c, []):
                phi_ge0_radj[s].append(c)
        q = deque(phi_ge0_sinks)
        while q:
            s = q.popleft()
            for c in phi_ge0_radj.get(s, []):
                new_r = phi_ge0_rank[s] + 1
                if c not in phi_ge0_rank or new_r > phi_ge0_rank[c]:
                    phi_ge0_rank[c] = new_r
                    q.append(c)
        max_phi_ge0_rank = max(phi_ge0_rank.values()) if phi_ge0_rank else 0

        # FINAL VERIFICATION: (Φ, rank_in_ΔΦ≥0) is strictly decreasing on ALL edges
        total_viols = 0
        for c, s, pos, dfc in tp_edges:
            dphi = phi.get(s, 0) - phi.get(c, 0)
            if dphi > 0:
                # Φ increased — need rank to compensate (impossible for strict decrease)
                # Actually in lex order, if Φ increases, the pair increases regardless of rank.
                # So we need ΔΦ ≤ 0 for the first component to not increase.
                total_viols += 1
            elif dphi == 0:
                rc = phi_ge0_rank.get(c, 0)
                rs = phi_ge0_rank.get(s, 0)
                if rs >= rc:
                    total_viols += 1

        elapsed = time.time() - t0
        print(f"\nn={n}: {len(tp_edges)} TP edges | "
              f"ΔΦ>0: {phi_gt0_cnt}, ΔΦ=0: {phi_eq0_cnt}, ΔΦ<0: {len(phi_lt0_edges)}")
        print(f"  ΔΦ≥0 subgraph: {len(phi_ge0_edges)} edges, "
              f"DAG: {'YES' if not has_cycle else 'NO (CYCLE FOUND!)'}, "
              f"max rank: {max_phi_ge0_rank}")
        print(f"  (Φ, rank_ΔΦ≥0) strictly decreasing: "
              f"{'YES — PROOF COMPLETE!' if total_viols == 0 else f'NO, {total_viols} violations'}")
        print(f"  g range: [0, {max(g.values()) if g else 0}]  "
              f"Φ range: [{min(phi.values())}, {max(phi.values())}]")
        print(f"  Time: {elapsed:.1f}s")

        if has_cycle:
            # Find and print a cycle
            print(f"  CYCLE FOUND — investigating...")

        if total_viols > 0 and not has_cycle:
            # The ΔΦ≥0 is DAG but ΔΦ>0 edges exist — so lex doesn't work directly
            # because ΔΦ>0 means first component INCREASES
            # UNLESS we can show ΔΦ>0 edges are always into the ΔΦ≥0 DAG
            # with rank drop ≥ ΔΦ * max_rank_jump...
            # Actually, redefine: use Ψ = Φ * (max_rank + 1) + rank
            # Then ΔΨ = ΔΦ * (max_rank + 1) + Δrank
            # On ΔΦ<0: ΔΨ ≤ -1 * (max_rank + 1) + max_rank < 0 ✓
            # On ΔΦ=0: ΔΨ = Δrank < 0 (since DAG) ✓
            # On ΔΦ=+1: ΔΨ = (max_rank + 1) + Δrank. Need Δrank ≤ -(max_rank+1)
            # That's impossible unless rank drops by max_rank+1...
            print(f"  Note: ΔΦ>0 edges mean simple lex doesn't work.")
            print(f"  Trying scalar: Ψ = (R+1)*Φ - rank where R = max_rank")
            R = max_phi_ge0_rank
            scalar_viols = 0
            for c, s, pos, dfc in tp_edges:
                dphi = phi.get(s, 0) - phi.get(c, 0)
                rc = phi_ge0_rank.get(c, 0)
                rs = phi_ge0_rank.get(s, 0)
                dpsi = (R + 1) * dphi - (rs - rc)  # want < 0 (decreasing rank = rs < rc, so negative)
                # Actually: Ψ = (R+1)*Φ + rank. Want Ψ strictly decreasing.
                # ΔΨ = (R+1)*ΔΦ + Δrank. On ΔΦ<0: ≤ -(R+1) + R < 0 ✓
                # On ΔΦ=0: = Δrank < 0 (DAG) ✓
                # On ΔΦ=+1: = (R+1) + Δrank. Need Δrank < -(R+1), impossible.
                # So need Ψ = (R+1)*(-Φ) + rank = -(R+1)*Φ + rank? No...
                pass
            # The issue: ΔΦ>0 means NO scalar combination works.
            # We need to handle ΔΦ>0 edges separately.

            # KEY: if ΔΦ>0 edges are NEVER on any cycle of the ΔΦ≥0 subgraph
            # (which is DAG), then removing them still gives a DAG.
            # But they ARE in the ΔΦ≥0 subgraph!
            # So maybe: show that the ΔΦ>0 edges all point "backward" in the
            # ΔΦ=0 DAG ranking, i.e., from high rank to low rank in the
            # constant-Φ subgraph. If so, the combined is still a DAG.

            # Check: on ΔΦ>0 edges, is rank_ΔΦ=0 always decreasing?
            # First compute rank in ΔΦ=0 subgraph
            phi_eq0_adj = defaultdict(list)
            phi_eq0_nodes = set()
            for c, s, pos, dfc, dphi in phi_ge0_edges:
                if dphi == 0:
                    phi_eq0_adj[c].append(s)
                    phi_eq0_nodes.add(c)
                    phi_eq0_nodes.add(s)

            phi_eq0_out = {c: len(phi_eq0_adj.get(c, [])) for c in phi_eq0_nodes}
            phi_eq0_sinks = [c for c in phi_eq0_nodes if phi_eq0_out[c] == 0]
            phi_eq0_rank = {c: 0 for c in phi_eq0_sinks}
            phi_eq0_radj = defaultdict(list)
            for c in phi_eq0_nodes:
                for s in phi_eq0_adj.get(c, []):
                    phi_eq0_radj[s].append(c)
            q = deque(phi_eq0_sinks)
            while q:
                s = q.popleft()
                for c in phi_eq0_radj.get(s, []):
                    new_r = phi_eq0_rank[s] + 1
                    if c not in phi_eq0_rank or new_r > phi_eq0_rank[c]:
                        phi_eq0_rank[c] = new_r
                        q.append(c)

            # On ΔΦ>0 edges (source has ΔΦ=0 rank, dest has ΔΦ=0 rank+something)
            # Check rank relationship
            rank_gt0_analysis = []
            for c, s, pos, dfc, dphi in phi_ge0_edges:
                if dphi > 0:
                    rc = phi_eq0_rank.get(c, -1)
                    rs = phi_eq0_rank.get(s, -1)
                    rank_gt0_analysis.append((rc, rs, dphi, pos))
            print(f"  ΔΦ>0 edges: ΔΦ=0-rank analysis:")
            for rc, rs, dphi, pos in rank_gt0_analysis[:15]:
                print(f"    pos={pos}: rank {rc} → {rs} (ΔΦ={dphi:+d})")


if __name__ == '__main__':
    main()
