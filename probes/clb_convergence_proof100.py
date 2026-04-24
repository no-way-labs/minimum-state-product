#!/usr/bin/env python3
"""
CONVERGENCE PROOF 100: Full-lookahead potential Φ_full = max reachable fc
==========================================================================
KEY IDEA: Define g_full(c) = max(fc(s) - fc(c)) over all TP-reachable s from c.
Then Φ_full(c) = fc(c) + g_full(c) = max fc(s) over all TP-reachable s from c.

Φ_full is guaranteed NON-INCREASING on all TP edges (by construction).
If it STRICTLY DECREASES on all TP edges (or the constant subgraph is a DAG),
we have the convergence proof.

COMPUTATION: iterate g_{k+1}(c) = max(g_k(c), max over neighbors s of (dfc + g_k(s)))
starting from g_0 = 0. Since fc ∈ [0, n], this converges in ≤ n iterations.
If ANY g value exceeds n, the TP graph has a cycle (IMPOSSIBLE by verification).

If Φ_full has fewer constant edges than Φ, we're making progress.
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

        if len(bad_list) > 250000:
            print(f"\nn={n}: skipping ({len(bad_list)} bad configs)")
            continue

        # Build TP edges
        tp_adj = defaultdict(list)  # c -> [(s, dfc)]
        tp_edges = []
        tp_nodes = set()
        fc_cache = {}
        for c in bad_list:
            fc_cache[c] = fc(c, n)
            tp_nodes.add(c)

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
                            if succ not in fc_cache:
                                fc_cache[succ] = fc(succ, n)
                            dfc = fc_cache[succ] - fc_cache[c]
                            tp_edges.append((c, succ, i, dfc))
                            tp_adj[c].append((succ, dfc))
                            tp_nodes.add(succ)

        # Compute g_full via iteration
        # g[c] = max(fc(s) - fc(c)) over all TP-reachable s
        # Initialize: g[c] = 0 for all
        g = {c: 0 for c in tp_nodes}
        max_iters = 2 * n  # upper bound

        for iteration in range(max_iters):
            changed = False
            max_g_val = 0
            for c in tp_nodes:
                for s, dfc in tp_adj.get(c, []):
                    new_g = dfc + g[s]
                    if new_g > g[c]:
                        g[c] = new_g
                        changed = True
                max_g_val = max(max_g_val, g[c])
            if not changed:
                break
            if max_g_val > 2 * n:
                print(f"n={n}: g_full DIVERGES at iteration {iteration} (max_g={max_g_val})")
                print(f"  This would indicate a cycle (impossible by verification)")
                break
        else:
            print(f"n={n}: WARNING — did not converge in {max_iters} iterations")
            continue

        g_dist = Counter(g.values())
        print(f"\nn={n}: {len(tp_edges)} TP edges, converged in {iteration+1} iterations")
        print(f"  g_full distribution: {dict(sorted(g_dist.items()))}")

        # Compute Φ_full = fc + g_full
        phi = {c: fc_cache[c] + g[c] for c in tp_nodes}

        # Verify non-increasing
        viols = 0
        const_cnt = 0
        dec_cnt = 0
        for c, s, pos, dfc in tp_edges:
            dphi = phi.get(s, 0) - phi.get(c, 0)
            if dphi > 0:
                viols += 1
            elif dphi == 0:
                const_cnt += 1
            else:
                dec_cnt += 1

        print(f"  Φ_full non-increasing: {'YES' if viols == 0 else f'NO ({viols} violations)'}")
        print(f"  Constant: {const_cnt}, Decrease: {dec_cnt}")

        if viols > 0:
            # Show violations
            for c, s, pos, dfc in tp_edges:
                dphi = phi.get(s, 0) - phi.get(c, 0)
                if dphi > 0:
                    L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]; out = s[pos]
                    print(f"  VIOL: pos={pos} ({L},{S},{R})->{out} Δfc={dfc:+d} "
                          f"g:{g[c]}→{g[s]} Φ:{phi[c]}→{phi[s]}")
                    if viols <= 5:
                        break
            continue

        # Φ_full is non-increasing! Now check if constant subgraph is a DAG.
        const_adj = defaultdict(list)
        const_nodes = set()
        for c, s, pos, dfc in tp_edges:
            if phi[s] == phi[c]:
                const_adj[c].append(s)
                const_nodes.add(c)
                const_nodes.add(s)

        # DAG check via DFS
        WHITE, GRAY, BLACK = 0, 1, 2
        color = {c: WHITE for c in const_nodes}
        is_dag = True
        for start in const_nodes:
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
                for s in const_adj.get(node, []):
                    if color[s] == GRAY:
                        is_dag = False
                        break
                    if color[s] == WHITE:
                        stack.append((s, False))
                if not is_dag:
                    break
            if not is_dag:
                break

        # Compute rank of constant subgraph
        const_out = {c: len(const_adj.get(c, [])) for c in const_nodes}
        const_sinks = [c for c in const_nodes if const_out[c] == 0]
        const_rank = {c: 0 for c in const_sinks}
        const_radj = defaultdict(list)
        for c in const_nodes:
            for s in const_adj.get(c, []):
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

        # Verify lex (Φ_full, const_rank) is strictly decreasing on ALL TP edges
        lex_viols = 0
        for c, s, pos, dfc in tp_edges:
            dphi = phi[s] - phi[c]
            if dphi > 0:
                lex_viols += 1
            elif dphi == 0:
                rc = const_rank.get(c, 0)
                rs = const_rank.get(s, 0)
                if rs >= rc:
                    lex_viols += 1

        phi_range = (min(phi.values()), max(phi.values()))
        print(f"  Constant-Φ_full subgraph: {const_cnt} edges, "
              f"DAG: {'YES' if is_dag else 'NO'}, max rank: {max_const_rank}")
        print(f"  Lex (Φ_full, const_rank) strictly decreasing: "
              f"{'YES — PROOF COMPLETE!' if lex_viols == 0 else f'NO ({lex_viols} violations)'}")
        print(f"  Φ_full range: {phi_range}")

        # Analyze constant-Φ edges by position and entry type
        const_dfc_dist = Counter()
        const_pos_dist = Counter()
        for c, s, pos, dfc in tp_edges:
            if phi[s] == phi[c]:
                const_dfc_dist[dfc] += 1
                const_pos_dist[pos] += 1
        print(f"  Constant-Φ_full by Δfc: {dict(sorted(const_dfc_dist.items()))}")
        if len(const_pos_dist) <= 15:
            print(f"  Constant-Φ_full by position: {dict(sorted(const_pos_dist.items()))}")

        print(f"  Time: {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
