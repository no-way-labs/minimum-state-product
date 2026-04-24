#!/usr/bin/env python3
"""
CONVERGENCE PROOF 101: Analytical characterization of g_full
=============================================================
g_full(c) ∈ {0,1,2,3,4} for all n and all configs c.
Goal: find an n-independent formula for g_full(c) based on config structure.

Also: push verification to n=13 with optimized code.

Key insight: Φ_full = fc + g_full is non-increasing on ALL TP edges
(proved by definition: max reachable fc can only decrease along edges).
This is ANALYTICALLY proved — no computation needed!

So the only remaining analytical challenge is:
  Prove the constant-Φ_full subgraph is a DAG.

Can we characterize g_full to make the constant subgraph easier to analyze?
"""
import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter


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

    for n_val in range(5, 14):
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        if len(bad_list) > 800000:
            print(f"\nn={n}: skipping ({len(bad_list)} bad)")
            continue

        # Build TP adjacency (forward and backward)
        tp_fwd = defaultdict(list)  # c -> [(s, dfc)]
        tp_bwd = defaultdict(list)  # s -> [(c, -dfc)] = (c, fc(c)-fc(s))
        tp_nodes = set()
        fc_cache = {}

        for c in bad_list:
            fc_cache[c] = fc(c, n)
            tp_nodes.add(c)

        tp_edge_list = []
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
                            tp_fwd[c].append((succ, dfc))
                            tp_bwd[succ].append((c, -dfc))
                            tp_edge_list.append((c, succ, i, dfc))
                            tp_nodes.add(succ)

        # Compute g_full via Bellman-Ford style iteration
        g = {c: 0 for c in tp_nodes}
        for iteration in range(2 * n):
            changed = False
            for c in tp_nodes:
                for s, dfc in tp_fwd.get(c, []):
                    new_g = dfc + g[s]
                    if new_g > g[c]:
                        g[c] = new_g
                        changed = True
            if not changed:
                break

        g_dist = Counter(g.values())
        max_g = max(g.values()) if g else 0

        # Characterize g_full by boundary state
        bnd_g = defaultdict(list)
        for c in tp_nodes:
            bnd = (c[0], c[1], c[n-2], c[n-1])
            bnd_g[bnd].append(g[c])

        # For each boundary state, what g values are possible?
        bnd_g_range = {}
        for bnd, gvals in bnd_g.items():
            bnd_g_range[bnd] = (min(gvals), max(gvals))

        # Which boundary states have g > 0?
        bnd_with_high_g = {bnd: maxg for bnd, (ming, maxg) in bnd_g_range.items() if maxg > 0}

        # Check: does g depend only on boundary?
        g_by_bnd = defaultdict(set)
        for c in tp_nodes:
            bnd = (c[0], c[1], c[n-2], c[n-1])
            g_by_bnd[bnd].add(g[c])
        multi_g_bnds = {bnd: gvals for bnd, gvals in g_by_bnd.items() if len(gvals) > 1}

        # Check: does g depend on boundary + fc?
        g_by_bnd_fc = defaultdict(set)
        for c in tp_nodes:
            bnd = (c[0], c[1], c[n-2], c[n-1])
            g_by_bnd_fc[(bnd, fc_cache[c])].add(g[c])
        multi_g_bnd_fc = {k: gvals for k, gvals in g_by_bnd_fc.items() if len(gvals) > 1}

        # Check: which configs have g=4?
        g4_configs = [c for c in tp_nodes if g[c] == 4]
        g3_configs = [c for c in tp_nodes if g[c] == 3]

        elapsed = time.time() - t0
        print(f"\nn={n}: {len(tp_edge_list)} TP edges, g converged iter {iteration+1}")
        print(f"  g_full range: [0, {max_g}]  dist: {dict(sorted(g_dist.items()))}")
        print(f"  Boundary states with max g > 0: {len(bnd_with_high_g)}/{len(bnd_g_range)}")
        print(f"  g depends only on boundary? {'YES' if not multi_g_bnds else f'NO ({len(multi_g_bnds)} multi-g)'}")
        print(f"  g depends on (boundary, fc)? {'YES' if not multi_g_bnd_fc else f'NO ({len(multi_g_bnd_fc)} multi-g)'}")

        if multi_g_bnds and len(multi_g_bnds) <= 20:
            for bnd, gvals in sorted(multi_g_bnds.items()):
                print(f"    bnd={bnd}: g ∈ {sorted(gvals)}")

        # g=4 configs: boundary state
        if g4_configs:
            g4_bnds = Counter((c[0], c[1], c[n-2], c[n-1]) for c in g4_configs)
            print(f"  g=4 configs ({len(g4_configs)}): boundary states = {dict(g4_bnds)}")

        # g=3 configs: boundary state
        if g3_configs and len(g3_configs) <= 200:
            g3_bnds = Counter((c[0], c[1], c[n-2], c[n-1]) for c in g3_configs)
            print(f"  g=3 configs ({len(g3_configs)}): boundary states = {dict(g3_bnds)}")

        # Trace the g=4 path from a g=4 config
        if g4_configs:
            c = g4_configs[0]
            print(f"  g=4 path from {c[:4]}...{c[-4:]}:")
            path = [c]
            cur = c
            for step in range(10):
                best_s = None
                best_gain = -1
                for s, dfc in tp_fwd.get(cur, []):
                    gain = dfc + g[s]
                    if gain > best_gain:
                        best_gain = gain
                        best_s = s
                        best_dfc = dfc
                if best_s is None or best_gain <= 0:
                    break
                print(f"    step {step}: Δfc={best_dfc:+d}, g={g[best_s]}, "
                      f"fc={fc_cache[best_s]}, bnd=({best_s[0]},{best_s[1]},{best_s[n-2]},{best_s[n-1]})")
                path.append(best_s)
                cur = best_s

        # KEY: what determines g_full=0 vs g_full>0?
        # Test: does g=0 iff "no anomalous entry reachable via TP"?
        # The 5 anomalous entries are the ONLY Δfc>0 edges.
        # So g>0 iff some anomalous entry fires on a TP-reachable config.

        # Test: does g=0 correlate with boundary state?
        g0_bnds = set()
        g_pos_bnds = set()
        for c in tp_nodes:
            bnd = (c[0], c[1], c[n-2], c[n-1])
            if g[c] == 0:
                g0_bnds.add(bnd)
            else:
                g_pos_bnds.add(bnd)
        g0_only = g0_bnds - g_pos_bnds
        gp_only = g_pos_bnds - g0_bnds
        both = g0_bnds & g_pos_bnds
        print(f"  Boundary: g=0 only: {len(g0_only)}, g>0 only: {len(gp_only)}, both: {len(both)}")
        if g0_only:
            print(f"    g=0-only boundaries: {sorted(g0_only)}")
        if gp_only:
            print(f"    g>0-only boundaries: {sorted(gp_only)}")

        print(f"  Time: {elapsed:.1f}s")


if __name__ == '__main__':
    main()
