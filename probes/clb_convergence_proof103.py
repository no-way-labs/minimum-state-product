#!/usr/bin/env python3
"""
CONVERGENCE PROOF 103: Characterize constant-Φ_full edges
==========================================================
For an analytical DAG proof, we need to understand WHY the constant-Φ_full
subgraph is acyclic. Constant edges are those where Δfc + Δg_full = 0.

Key questions:
1. What entry types appear on constant edges? (position, (L,S,R)→out)
2. What are the g_full transitions? (g_before → g_after)
3. Is there a "progress measure" that decreases on all constant edges?
4. Do constant edges have special structure (e.g., only at boundary positions)?

INSIGHT: g_full measures "how much of the A2→A3→A4 gain sequence is reachable."
Constant edges are "on the optimal path" — they achieve the max future fc gain.
"""
import sys, os, time
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

    for n_val in range(7, 13):
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        if len(bad_list) > 900000:
            print(f"\nn={n}: skipping ({len(bad_list)} bad)")
            continue

        # Build TP edges
        tp_fwd = defaultdict(list)
        tp_nodes = set()
        fc_cache = {}
        tp_edge_list = []

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
                        if succ not in fc_cache:
                            fc_cache[succ] = fc(succ, n)
                        e2s = exp2_count(succ, n)
                        i21s = int_21(succ, n)
                        ews = exp2_weight(succ, n)
                        if e2s == e2c and i21s == i21c and ews == ewc:
                            dfc = fc_cache[succ] - fc_cache[c]
                            tp_fwd[c].append((succ, dfc))
                            tp_edge_list.append((c, succ, i, dfc))
                            tp_nodes.add(succ)

        # Compute g_full via Bellman-Ford
        g = {c: 0 for c in tp_nodes}
        for iteration in range(2 * n + 5):
            changed = False
            for c in tp_nodes:
                for s, dfc in tp_fwd.get(c, []):
                    new_g = dfc + g[s]
                    if new_g > g[c]:
                        g[c] = new_g
                        changed = True
            if not changed:
                break

        phi = {c: fc_cache[c] + g[c] for c in tp_nodes}

        # Classify constant-Φ_full edges
        const_edges = []
        dec_edges = []
        for c, s, pos, dfc in tp_edge_list:
            dphi = phi[s] - phi[c]
            if dphi == 0:
                const_edges.append((c, s, pos, dfc))
            elif dphi < 0:
                dec_edges.append((c, s, pos, dfc))

        print(f"\n{'='*70}")
        print(f"n={n}: {len(const_edges)} constant + {len(dec_edges)} decreasing = {len(tp_edge_list)} total TP edges")

        # 1. Entry type distribution on constant edges
        entry_dist = Counter()
        for c, s, pos, dfc in const_edges:
            L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]; out = s[pos]
            entry_dist[(pos, L, S, R, out, dfc)] += 1

        # Normalize position to type
        pos_type_dist = Counter()
        for c, s, pos, dfc in const_edges:
            L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]; out = s[pos]
            if pos == 0:
                ptype = "bot"
            elif pos == 1:
                ptype = "low"
            elif pos == 2:
                ptype = "P2"
            elif pos == n-2:
                ptype = "high"
            elif pos == n-1:
                ptype = "top"
            else:
                ptype = f"mid"
            pos_type_dist[(ptype, L, S, R, out, dfc)] += 1

        print(f"\n  Constant-Φ edges by (pos_type, L, S, R, out, Δfc):")
        for key, cnt in sorted(pos_type_dist.items(), key=lambda x: (-x[1], x[0])):
            ptype, L, S, R, out, dfc = key
            print(f"    {ptype:4s} ({L},{S},{R})→{out} Δfc={dfc:+d}: {cnt}")

        # 2. g_full transitions on constant edges
        g_trans = Counter()
        for c, s, pos, dfc in const_edges:
            g_trans[(g[c], g[s])] += 1
        print(f"\n  g_full transitions (g_before → g_after) on constant edges:")
        for (gb, ga), cnt in sorted(g_trans.items()):
            print(f"    g={gb} → g={ga} (Δg={ga-gb:+d}): {cnt}")

        # 3. Position distribution
        pos_dist = Counter(pos for _, _, pos, _ in const_edges)
        print(f"\n  Position distribution: {dict(sorted(pos_dist.items()))}")

        # 4. Which positions have Δfc>0 constant edges (anomalous)?
        anom_const = [(c, s, pos, dfc) for c, s, pos, dfc in const_edges if dfc > 0]
        anom_pos = Counter(pos for _, _, pos, _ in anom_const)
        print(f"\n  Anomalous (Δfc>0) constant edges: {len(anom_const)}")
        print(f"  By position: {dict(sorted(anom_pos.items()))}")

        # 5. fc values on constant edges
        fc_trans = Counter()
        for c, s, pos, dfc in const_edges:
            fc_trans[(fc_cache[c], fc_cache[s])] += 1
        print(f"\n  fc transitions on constant edges:")
        for (fc1, fc2), cnt in sorted(fc_trans.items()):
            if cnt >= 5:
                print(f"    fc={fc1} → fc={fc2}: {cnt}")

        # 6. Key question: on constant edges, does the INTERIOR of the config change?
        # Interior = c[3..n-3] (positions not in boundary)
        if n >= 8:
            interior_changes = 0
            for c, s, pos, dfc in const_edges:
                if 3 <= pos <= n-3:
                    interior_changes += 1
            print(f"\n  Interior-position (3..{n-3}) constant edges: {interior_changes}/{len(const_edges)}")

            # For interior constant edges, what entries?
            int_entries = Counter()
            for c, s, pos, dfc in const_edges:
                if 3 <= pos <= n-3:
                    L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]; out = s[pos]
                    int_entries[(L, S, R, out, dfc)] += 1
            if int_entries:
                print(f"  Interior constant edge entries:")
                for key, cnt in sorted(int_entries.items(), key=lambda x: -x[1]):
                    L, S, R, out, dfc = key
                    print(f"    ({L},{S},{R})→{out} Δfc={dfc:+d}: {cnt}")

        # 7. Boundary state on constant edges
        bnd_const = Counter()
        for c, s, pos, dfc in const_edges:
            bnd_c = (c[0], c[1], c[n-2], c[n-1])
            bnd_s = (s[0], s[1], s[n-2], s[n-1])
            bnd_const[(bnd_c, bnd_s)] += 1
        # How many distinct boundary transitions?
        print(f"\n  Boundary transitions on constant edges: {len(bnd_const)} distinct")

        # Boundary-changing vs boundary-preserving
        bnd_changing = sum(cnt for (bc, bs), cnt in bnd_const.items() if bc != bs)
        bnd_same = sum(cnt for (bc, bs), cnt in bnd_const.items() if bc == bs)
        print(f"  Boundary-changing: {bnd_changing}, boundary-preserving: {bnd_same}")

        # 8. For boundary-preserving constant edges: what positions fire?
        bnd_pres_pos = Counter()
        for c, s, pos, dfc in const_edges:
            bnd_c = (c[0], c[1], c[n-2], c[n-1])
            bnd_s = (s[0], s[1], s[n-2], s[n-1])
            if bnd_c == bnd_s:
                bnd_pres_pos[pos] += 1
        print(f"  Boundary-preserving by position: {dict(sorted(bnd_pres_pos.items()))}")

        # 9. KEY: Can constant edges form a cycle?
        # Check: on constant edges, does fc monotonically relate to something?
        # On constant edges, g_full = Φ_full - fc. If Φ_full is constant along a path
        # of constant edges, then g_full = P - fc for some fixed P.
        # So g_full and fc are inversely related.
        # For a cycle, we'd need fc to return to the same value.
        # Along the way, fc goes up (anomalous) and down (normal).
        # Is there a SECONDARY quantity that is monotone on constant edges?

        # Test: position of the fired entry — does it always go in one direction?
        # On constant-edge paths, track the positions
        # Build the constant subgraph
        const_adj = defaultdict(list)
        for c, s, pos, dfc in const_edges:
            const_adj[c].append((s, pos, dfc))

        # For each config, what's the maximum chain length in constant subgraph?
        # Already know it's a DAG with rank 7n-30, so this is finite.

        # 10. MOST IMPORTANT: Characterize by Φ_full level
        phi_level_cnt = Counter()
        for c, s, pos, dfc in const_edges:
            phi_level_cnt[phi[c]] += 1
        print(f"\n  Constant edges by Φ_full level: {dict(sorted(phi_level_cnt.items()))}")

        # 11. Within each Φ_full level, what's the DAG rank?
        # Group constant edges by Φ_full level
        phi_levels = sorted(phi_level_cnt.keys())
        for P in phi_levels:
            level_edges = [(c, s, pos, dfc) for c, s, pos, dfc in const_edges if phi[c] == P]
            level_nodes = set()
            level_adj = defaultdict(list)
            for c, s, pos, dfc in level_edges:
                level_adj[c].append(s)
                level_nodes.add(c)
                level_nodes.add(s)
            # Compute rank within this level
            from collections import deque
            level_out = {c: len(level_adj.get(c, [])) for c in level_nodes}
            level_sinks = [c for c in level_nodes if level_out[c] == 0]
            level_rank = {c: 0 for c in level_sinks}
            level_radj = defaultdict(list)
            for c in level_nodes:
                for s in level_adj.get(c, []):
                    level_radj[s].append(c)
            q = deque(level_sinks)
            while q:
                s = q.popleft()
                for c in level_radj.get(s, []):
                    new_r = level_rank[s] + 1
                    if c not in level_rank or new_r > level_rank[c]:
                        level_rank[c] = new_r
                        q.append(c)
            max_level_rank = max(level_rank.values()) if level_rank else 0

            # fc range at this level
            fc_at_level = Counter(fc_cache[c] for c in level_nodes)
            g_at_level = Counter(g[c] for c in level_nodes)
            print(f"    Φ={P}: {len(level_edges)} edges, {len(level_nodes)} nodes, "
                  f"rank={max_level_rank}, fc∈{sorted(fc_at_level.keys())}, "
                  f"g∈{sorted(g_at_level.keys())}")

        elapsed = time.time() - t0
        print(f"\n  Time: {elapsed:.1f}s")


if __name__ == '__main__':
    main()
