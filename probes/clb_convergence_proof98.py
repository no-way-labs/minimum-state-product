#!/usr/bin/env python3
"""
CONVERGENCE PROOF 98: Rank-3 path characterization + DAG proof attempt
=======================================================================
KEY FACT: The Δfc≥0 subgraph of the TP graph has rank ≤ 3 (verified n=5..12).
This means: from any config, following only Δfc≥0 TP edges, you reach a dead
end within 3 steps.

GOAL: Characterize ALL rank-3 paths analytically. If they all terminate at
dead ends with a specific structure, we get the proof.

STRATEGY:
1. Enumerate all rank-3 paths (entry sequences + boundary states)
2. Show rank-3 endpoints are "dead ends" (no outgoing Δfc≥0 or Δfc=0 edges)
3. Use fc + rank_up as a potential: Φ(c) = K*fc(c) + rank_up(c)
   where rank_up = max Δfc≥0 path length from c.
   On Δfc<0 edge: ΔΦ ≤ K*(-1) + 3 < 0 if K≥4.
   On Δfc≥0 edge: rank_up decreases by 1, fc increases by ≤2,
   so ΔΦ ≤ K*2 - 1. Need this < 0 too → K < 1/2. Contradiction!

So this direct approach fails. But maybe a REFINED rank works:
rank_weighted = Σ (max fc gain from here on Δfc≥0 subpath).
Then on Δfc≥0 edge with dfc=d: fc changes by d, rank_weighted decreases by ≥d.
So Φ = fc + rank_weighted doesn't increase on Δfc≥0 edges.
And Φ = fc decreases on Δfc<0 edges (rank_weighted could increase...).

Better: use MULTI-LEVEL lexicographic with fc as primary.
On Δfc<0 edges: fc decreases → Φ decreases.
On Δfc=0 edges: need secondary quantity that decreases.
On Δfc>0 edges (rank ≤ 3): need tertiary that decreases.

Actually: on Δfc≥0 path of rank r, the TERMINAL fc gain = total Δfc ≤ 4.
So fc can increase by at most 4 before it must decrease. This means:
  Define Φ(c) = fc(c) + max_future_fc_gain(c)
where max_future_fc_gain(c) = max total Δfc on any Δfc≥0 path from c.

Then: Φ(c) = fc(c) + g(c) where g(c) ∈ [0, 4].
On Δfc≥0 edge c→s with dfc=d≥0: g(s) ≤ g(c) - d (the max future gain decreases
by at least d, since we've "used up" d of the budget).
So ΔΦ = d + (g(s) - g(c)) ≤ d + (-d) = 0.
But when is ΔΦ < 0? Only when g(s) < g(c) - d, which isn't guaranteed.

So Φ is non-increasing on Δfc≥0 edges but could be constant (=0).
On Δfc<0 edges: ΔΦ = dfc + Δg ≤ dfc + 4 ≤ -1 + 4 = 3. Not guaranteed negative!

Hmm. So even fc + max_future_gain doesn't work.

BUT: maybe we can show that on Δfc=0 edges, max_future_gain STRICTLY decreases?
That would handle the Δfc=0 case. And on Δfc>0 edges (anomalous), rank_up decreases.

Let's just compute everything and see what the structure looks like.
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

    for n_val in [7, 8, 9, 10]:
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        # Build TP edges with Δfc
        tp_adj = defaultdict(list)
        tp_adj_ge0 = defaultdict(list)
        tp_adj_eq0 = defaultdict(list)
        tp_adj_gt0 = defaultdict(list)
        tp_adj_lt0 = defaultdict(list)
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
                            tp_adj[c].append((succ, dfc, i))
                            tp_nodes.add(c); tp_nodes.add(succ)
                            if dfc >= 0:
                                tp_adj_ge0[c].append((succ, dfc, i))
                            if dfc == 0:
                                tp_adj_eq0[c].append((succ, i))
                            if dfc > 0:
                                tp_adj_gt0[c].append((succ, dfc, i))
                            if dfc < 0:
                                tp_adj_lt0[c].append((succ, dfc, i))

        print(f"\n{'='*70}")
        print(f"n={n}: {len(tp_edges)} TP edges, {len(tp_nodes)} TP nodes")

        # Compute rank in Δfc≥0 subgraph (max path length FROM each node)
        # Use reverse BFS from sinks
        rank_ge0 = {}
        # First find sinks (no outgoing Δfc≥0 edges)
        for c in tp_nodes:
            if not tp_adj_ge0.get(c):
                rank_ge0[c] = 0
        q = deque(rank_ge0.keys())
        # Reverse adjacency for Δfc≥0
        tp_radj_ge0 = defaultdict(list)
        for c in tp_nodes:
            for s, dfc, pos in tp_adj_ge0.get(c, []):
                tp_radj_ge0[s].append(c)

        while q:
            s = q.popleft()
            for c in tp_radj_ge0.get(s, []):
                new_r = rank_ge0[s] + 1
                if c not in rank_ge0 or new_r > rank_ge0[c]:
                    rank_ge0[c] = new_r
                    q.append(c)

        max_rank = max(rank_ge0.values()) if rank_ge0 else 0
        rank_dist = Counter(rank_ge0.values())
        print(f"  Δfc≥0 rank distribution: {dict(sorted(rank_dist.items()))}")
        print(f"  Max rank: {max_rank}")

        # Compute max future fc gain from each node (on Δfc≥0 paths)
        g = {}  # g[c] = max total Δfc along any Δfc≥0 path from c
        for c in tp_nodes:
            if not tp_adj_ge0.get(c):
                g[c] = 0
        # BFS from sinks backward
        q = deque([c for c in g])
        while q:
            s = q.popleft()
            for c in tp_radj_ge0.get(s, []):
                # Edge c→s has some dfc ≥ 0
                for ss, dfc, pos in tp_adj_ge0.get(c, []):
                    if ss == s:
                        new_g = dfc + g.get(s, 0)
                        if c not in g or new_g > g[c]:
                            g[c] = new_g
                            q.append(c)

        max_g = max(g.values()) if g else 0
        g_dist = Counter(g.values())
        print(f"  Max future fc gain (g) distribution: {dict(sorted(g_dist.items()))}")

        # Test potential Φ = fc + g on ALL TP edges
        phi_viols = 0
        phi_const = 0  # edges where Φ stays constant
        phi_dec = 0
        for c, s, pos, dfc in tp_edges:
            phi_c = fc(c, n) + g.get(c, 0)
            phi_s = fc(s, n) + g.get(s, 0)
            if phi_s > phi_c:
                phi_viols += 1
            elif phi_s == phi_c:
                phi_const += 1
            else:
                phi_dec += 1
        print(f"  Φ = fc + g: {phi_viols} violations, {phi_const} constant, {phi_dec} decrease")

        # Analyze constant-Φ edges
        const_adj = defaultdict(list)
        const_nodes = set()
        for c, s, pos, dfc in tp_edges:
            phi_c = fc(c, n) + g.get(c, 0)
            phi_s = fc(s, n) + g.get(s, 0)
            if phi_s == phi_c:
                const_adj[c].append((s, pos, dfc))
                const_nodes.add(c)
                const_nodes.add(s)

        # Is the constant-Φ subgraph a DAG?
        # Compute its rank
        const_out = {c: len(const_adj.get(c, [])) for c in const_nodes}
        const_sinks = [c for c in const_nodes if const_out[c] == 0]
        const_rank = {c: 0 for c in const_sinks}
        const_radj = defaultdict(list)
        for c in const_nodes:
            for s, _, _ in const_adj.get(c, []):
                const_radj[s].append(c)
        q = deque(const_sinks)
        while q:
            s = q.popleft()
            for c in const_radj.get(s, []):
                new_r = const_rank[s] + 1
                if c not in const_rank or new_r > const_rank[c]:
                    const_rank[c] = new_r
                    q.append(c)
        max_const_rank = max(const_rank.values()) if const_rank else 0
        print(f"  Constant-Φ subgraph: {sum(len(v) for v in const_adj.values())} edges, "
              f"max rank = {max_const_rank}")

        # What Δfc values appear on constant-Φ edges?
        const_dfc_dist = Counter()
        for c, s, pos, dfc in tp_edges:
            phi_c = fc(c, n) + g.get(c, 0)
            phi_s = fc(s, n) + g.get(s, 0)
            if phi_s == phi_c:
                const_dfc_dist[dfc] += 1
        print(f"  Constant-Φ edges by Δfc: {dict(sorted(const_dfc_dist.items()))}")

        # Characterize the constant-Φ edges by position
        const_pos_dist = Counter()
        const_entry_types = Counter()
        for c, s, pos, dfc in tp_edges:
            phi_c = fc(c, n) + g.get(c, 0)
            phi_s = fc(s, n) + g.get(s, 0)
            if phi_s == phi_c:
                const_pos_dist[pos] += 1
                L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]; out = s[pos]
                const_entry_types[(pos, L, S, R, out, dfc)] += 1
        print(f"  Constant-Φ by position: {dict(sorted(const_pos_dist.items()))}")
        print(f"  Constant-Φ entry types:")
        for (pos, L, S, R, out, dfc), cnt in sorted(const_entry_types.items()):
            if cnt > 0:
                print(f"    pos={pos} ({L},{S},{R})->{out} Δfc={dfc:+d}: {cnt}")

        # KEY: On constant-Φ edges, dfc + Δg = 0, so Δg = -dfc.
        # If dfc = 0, then Δg = 0 (g stays constant).
        # If dfc > 0, then Δg = -dfc < 0 (g decreases by dfc — uses up future gain).
        # If dfc < 0, then Δg = -dfc > 0 (g increases by |dfc|).
        # The last case seems problematic: fc decreases but g increases by same amount.

        # So constant-Φ edges can have dfc < 0 WITH g increasing.
        # This means within the constant-Φ subgraph, both dfc=0 and dfc<0 edges exist.

        # For the constant-Φ subgraph to be a DAG, we need ANOTHER quantity.
        # Within constant-Φ, both fc and g are "balanced" (Δfc + Δg = 0).
        # What else decreases?

        # Test: does rank_ge0 strictly decrease on constant-Φ edges?
        rank_viols_const = 0
        rank_const_const = 0
        for c, s, pos, dfc in tp_edges:
            phi_c = fc(c, n) + g.get(c, 0)
            phi_s = fc(s, n) + g.get(s, 0)
            if phi_s == phi_c:
                rc = rank_ge0.get(c, 0)
                rs = rank_ge0.get(s, 0)
                if rs >= rc:
                    rank_viols_const += 1
                if rs == rc:
                    rank_const_const += 1
        print(f"  rank_ge0 on constant-Φ edges: {rank_viols_const} non-decreasing "
              f"({rank_const_const} constant)")

        # Test: (Φ, rank_ge0) lexicographic
        lex_viols = 0
        for c, s, pos, dfc in tp_edges:
            key_c = (fc(c, n) + g.get(c, 0), rank_ge0.get(c, 0))
            key_s = (fc(s, n) + g.get(s, 0), rank_ge0.get(s, 0))
            if key_s >= key_c:
                lex_viols += 1
        print(f"  Lex (Φ, rank_ge0) desc: {lex_viols} violations")

        # Test (Φ, -fc) lexicographic (prefer lower fc when Φ tied)
        lex_viols2 = 0
        for c, s, pos, dfc in tp_edges:
            key_c = (fc(c, n) + g.get(c, 0), -fc(c, n))
            key_s = (fc(s, n) + g.get(s, 0), -fc(s, n))
            if key_s >= key_c:
                lex_viols2 += 1
        print(f"  Lex (Φ, -fc) desc: {lex_viols2} violations")

        # Test (Φ, g) lexicographic
        lex_viols3 = 0
        for c, s, pos, dfc in tp_edges:
            key_c = (fc(c, n) + g.get(c, 0), g.get(c, 0))
            key_s = (fc(s, n) + g.get(s, 0), g.get(s, 0))
            if key_s >= key_c:
                lex_viols3 += 1
        print(f"  Lex (Φ, g) desc: {lex_viols3} violations")

        # Analyze Φ VIOLATIONS (ΔΦ > 0)
        print(f"\n  Φ = fc + g VIOLATIONS (ΔΦ > 0):")
        for c, s, pos, dfc in tp_edges:
            phi_c = fc(c, n) + g.get(c, 0)
            phi_s = fc(s, n) + g.get(s, 0)
            if phi_s > phi_c:
                L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]; out = s[pos]
                gc = g.get(c, 0); gs = g.get(s, 0)
                print(f"    pos={pos} ({L},{S},{R})->{out} Δfc={dfc:+d} "
                      f"g:{gc}→{gs} Φ:{phi_c}→{phi_s} "
                      f"bnd=({c[0]},{c[1]},{c[n-2]},{c[n-1]})")

        print(f"  Time: {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
