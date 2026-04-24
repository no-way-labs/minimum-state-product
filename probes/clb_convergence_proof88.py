#!/usr/bin/env python3
"""
CONVERGENCE PROOF 88: fc-based potential with anomalous correction
===================================================================
Key facts:
- Δfc>0 subgraph rank = 3 (CONSTANT across all n)
- Only 5 anomalous entries cause Δfc>0, all at boundary positions
- After 3 consecutive Δfc>0 steps, must take Δfc≤0

Strategy: find a potential combining fc with a correction for the anomalous
entries. Test:
1. Φ = -fc·C + rank_in_Δfc>0  (fc decrease = good, rank decrease on Δfc>0)
2. Φ = -fc·C + rank_in_Δfc≥0
3. Track the exact entry types on Δfc>0 edges to understand structure
4. Look at what happens IMMEDIATELY AFTER a Δfc>0 edge
"""
import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system, T_bot, T_mid, T_high, T_top
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


def dag_rank_from_sinks(adj, nodes):
    """Rank = max distance from sinks. Sink rank = 0."""
    radj = defaultdict(list)
    out_deg = defaultdict(int)
    for c in nodes:
        out_deg[c] = len(adj.get(c, []))
        for s in adj.get(c, []):
            radj[s].append(c)
    sinks = [c for c in nodes if out_deg[c] == 0]
    rank = {c: 0 for c in sinks}
    q = deque(sinks)
    while q:
        c = q.popleft()
        for p in radj[c]:
            new_r = rank[c] + 1
            if p not in rank or new_r > rank[p]:
                rank[p] = new_r
                q.append(p)
    return rank


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

        # Build TP subgraph with full annotation
        tp_edges = []  # (src, dst, pos, dfc, entry_type)
        tp_adj = defaultdict(list)
        tp_adj_pos = defaultdict(list)  # Δfc > 0
        tp_adj_ge0 = defaultdict(list)  # Δfc >= 0
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
                            tp_adj[c].append(succ)
                            tp_nodes.add(c)
                            tp_nodes.add(succ)
                            if dfc > 0:
                                tp_adj_pos[c].append(succ)
                            if dfc >= 0:
                                tp_adj_ge0[c].append(succ)

        for c in bad_list:
            tp_nodes.add(c)

        # Compute ranks
        rank_pos = dag_rank_from_sinks(tp_adj_pos, tp_nodes)
        rank_ge0 = dag_rank_from_sinks(tp_adj_ge0, tp_nodes)

        K_pos = max(rank_pos.values()) if rank_pos else 0
        K_ge0 = max(rank_ge0.values()) if rank_ge0 else 0
        fc_max = max(fc(c, n) for c in bad_list)

        elapsed = time.time() - t0
        print(f"\n{'='*70}")
        print(f"n={n}: {len(tp_edges)} TP edges, K_pos={K_pos}, K_ge0={K_ge0}, "
              f"fc_max={fc_max} ({elapsed:.1f}s)")

        # Test potential: Φ = -fc * (K_pos+1) + rank_pos
        # On Δfc<0 edge: ΔΦ = -Δfc*(K+1) + Δr_pos ≥ (K+1) + (-K) = 1. WRONG SIGN.
        # Actually I want Φ to DECREASE. So Φ = fc*(K+1) - rank_pos.
        # On Δfc<0: ΔΦ = (K+1)*Δfc - Δr_pos ≤ -(K+1) + K = -1. ✓
        # On Δfc≥0: need (K+1)*Δfc - Δr_pos < 0.
        #   Δfc≥0 edge: rank_pos(c) ≥ 1+rank_pos(c')? NO, only if Δfc>0.
        #   Δfc=0 edge is NOT in the Δfc>0 subgraph!
        # So use rank_ge0 instead:
        # Φ = fc*(K_ge0+1) - rank_ge0
        # On Δfc≥0: (K_ge0+1)*Δfc - Δr_ge0. r_ge0 decreases by ≥1.
        #   ΔΦ ≤ (K_ge0+1)*Δfc + 1... wait, Δr_ge0 ≤ -1, so -Δr_ge0 ≥ 1.
        #   ΔΦ = (K_ge0+1)*Δfc - Δr_ge0 ≤ (K_ge0+1)*2 + 1 = 2K_ge0+3. BAD!
        # Hmm. On Δfc≥0 edge: need ΔΦ < 0. But Δfc can be +2, adding 2*(K+1).

        # REVERSE: Φ = -(K_ge0+1)*fc + rank_ge0
        # On Δfc≥0: ΔΦ = -(K_ge0+1)*Δfc + Δr_ge0 ≤ 0 + (-1) = -1. ✓
        # On Δfc<0: ΔΦ = -(K_ge0+1)*Δfc + Δr_ge0 = (K_ge0+1)*|Δfc| + Δr_ge0
        #   Δr_ge0 can be up to K_ge0. ΔΦ ≤ (K_ge0+1)*|Δfc| + K_ge0. POSITIVE. BAD.

        # Neither direction works with simple linear combo of fc and rank.
        # The issue: on Δfc<0 edges, rank_ge0 can jump UP by up to K_ge0.

        # NEW IDEA: What if I use BOTH rank_ge0 and rank_le0?
        # For the Δfc≤0 subgraph, compute rank_le0.
        tp_adj_le0 = defaultdict(list)
        for c, succ, pos, dfc in tp_edges:
            if dfc <= 0:
                tp_adj_le0[c].append(succ)
        rank_le0 = dag_rank_from_sinks(tp_adj_le0, tp_nodes)
        K_le0 = max(rank_le0.values()) if rank_le0 else 0

        # Test: Φ = rank_ge0 + rank_le0. Does it decrease?
        # On Δfc≥0: Δr_ge0 ≤ -1. Δr_le0 ∈ [-K_le0, K_le0].
        #   ΔΦ ≤ -1 + K_le0. BAD if K_le0 ≥ 1.
        # So this also doesn't work.

        # WHAT ABOUT: the actual DAG rank of the full TP graph?
        # Since TP is a DAG, the DAG rank is a perfect potential.
        # The question is: can I CHARACTERIZE it?

        # Let me look at WHAT ENTRIES fire on Δfc>0 edges and their successors
        anom_entry_info = Counter()
        anom_next_dfc = Counter()
        for c, succ, pos, dfc in tp_edges:
            if dfc > 0:
                L = c[(pos - 1) % n]; S = c[pos]; R = c[(pos + 1) % n]
                out = succ[pos]
                anom_entry_info[(pos, L, S, R, out, dfc)] += 1
                # What are the successors of succ in TP?
                for s2 in tp_adj.get(succ, []):
                    dfc2 = fc(s2, n) - fc(succ, n)
                    anom_next_dfc[dfc2] += 1

        print(f"\n  Anomalous (Δfc>0) entry types:")
        for (pos, L, S, R, out, dfc), cnt in sorted(anom_entry_info.items()):
            print(f"    pos={pos} ({L},{S},{R})→{out} Δfc={dfc:+d}: {cnt} edges")

        print(f"\n  After anomalous edge, next Δfc:")
        for dfc2, cnt in sorted(anom_next_dfc.items()):
            print(f"    Δfc={dfc2:+d}: {cnt}")

        # What's the max number of consecutive Δfc>0 edges?
        max_consec_pos = 0
        # BFS: from each node, follow Δfc>0 edges
        for c in tp_nodes:
            if not tp_adj_pos.get(c):
                continue
            # DFS for max path length
            stack = [(c, 0)]
            while stack:
                node, depth = stack.pop()
                max_consec_pos = max(max_consec_pos, depth)
                for s in tp_adj_pos.get(node, []):
                    if depth + 1 <= 10:  # safety limit
                        stack.append((s, depth + 1))

        print(f"\n  Max consecutive Δfc>0 edges: {max_consec_pos}")

        # KEY TEST: after a Δfc>0 edge, must the NEXT step decrease fc?
        # i.e., every successor of a Δfc>0 target has Δfc≤0 on all outgoing TP edges?
        forced_down = 0
        not_forced = 0
        for c, succ, pos, dfc in tp_edges:
            if dfc > 0:
                all_down = True
                for s2 in tp_adj.get(succ, []):
                    dfc2 = fc(s2, n) - fc(succ, n)
                    if dfc2 > 0:
                        all_down = False
                        break
                if all_down:
                    forced_down += 1
                else:
                    not_forced += 1

        n_pos = sum(1 for _, _, _, d in tp_edges if d > 0)
        print(f"\n  After Δfc>0: forced all-down={forced_down}/{n_pos}, "
              f"not forced={not_forced}")

        # What's the max fc GAIN along any Δfc≥0 path?
        max_fc_gain = 0
        # BFS on Δfc≥0 edges tracking fc gain
        for c in tp_nodes:
            if not tp_adj_ge0.get(c):
                continue
            fc_c = fc(c, n)
            stack = [(c, 0)]
            visited = {c: 0}
            while stack:
                node, gain = stack.pop()
                max_fc_gain = max(max_fc_gain, gain)
                for s in tp_adj_ge0.get(node, []):
                    new_gain = gain + (fc(s, n) - fc(node, n))
                    if s not in visited or new_gain > visited[s]:
                        visited[s] = new_gain
                        if new_gain <= 20:  # safety
                            stack.append((s, new_gain))

        print(f"  Max fc gain along Δfc≥0 path: {max_fc_gain}")

        print(f"  Time: {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
