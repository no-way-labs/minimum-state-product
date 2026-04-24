#!/usr/bin/env python3
"""Deep analysis of P₀ oscillation and anomalous firing patterns.

Key questions:
1. On any path in the DAG, how many times does each anomalous entry fire?
2. Between consecutive firings of the SAME anomalous entry, what decreases?
3. What is the maximum number of anomalous firings on any DAG path?
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_high, T_top
from cup2_convergence_proof import T_mid_alt, build_system, classify, delta_fc, psi
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, deque


def main():
    print("ANOMALOUS FIRING DEPTH ANALYSIS")
    print("=" * 70)

    for nv in range(5, 12):
        prod = 4 * 3 ** (nv - 2)
        if prod > 100000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        # Build adjacency with edge labels
        adj = {c: [] for c in bad_set}
        edge_type = {}  # (src, dst) -> type
        for c in bad_set:
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append(succ)
                        cls = classify(Li, Si, Ri, out)
                        dfc = delta_fc(Li, Si, Ri, out)
                        edge_type[(c, succ)] = (cls, dfc, i)

        # Topological sort (Kahn's)
        in_deg = {c: 0 for c in bad_set}
        for c in bad_set:
            for s in adj[c]:
                in_deg[s] += 1

        topo_order = []
        q = deque(c for c in bad_set if in_deg[c] == 0)
        while q:
            c = q.popleft()
            topo_order.append(c)
            for s in adj[c]:
                in_deg[s] -= 1
                if in_deg[s] == 0:
                    q.append(s)

        assert len(topo_order) == len(bad_set), "NOT A DAG!"

        # For each node, compute:
        # max_anom[c] = max anomalous firings on any path ending at c
        # max_anom_by_type[c] = max firings of each anomalous type on any path ending at c
        max_anom = {c: 0 for c in bad_set}
        max_bot_up = {c: 0 for c in bad_set}    # T_bot(0,0,0)→1
        max_bot_down = {c: 0 for c in bad_set}  # T_bot(1,1,2)→0
        max_high = {c: 0 for c in bad_set}      # T_high(1,1,1)→2
        max_top = {c: 0 for c in bad_set}       # T_top(2,0,0)→1

        for c in topo_order:
            for s in adj[c]:
                cls, dfc, pos = edge_type[(c, s)]
                anom_inc = 1 if cls == "anomalous" else 0
                bu_inc = 1 if (cls == "anomalous" and pos == 0 and dfc == 2) else 0
                bd_inc = 1 if (cls == "anomalous" and pos == 0 and dfc == 1) else 0
                hi_inc = 1 if (cls == "anomalous" and pos == n-2) else 0
                tp_inc = 1 if (cls == "anomalous" and pos == n-1) else 0

                max_anom[s] = max(max_anom[s], max_anom[c] + anom_inc)
                max_bot_up[s] = max(max_bot_up[s], max_bot_up[c] + bu_inc)
                max_bot_down[s] = max(max_bot_down[s], max_bot_down[c] + bd_inc)
                max_high[s] = max(max_high[s], max_high[c] + hi_inc)
                max_top[s] = max(max_top[s], max_top[c] + tp_inc)

        max_total = max(max_anom.values())
        max_bu = max(max_bot_up.values())
        max_bd = max(max_bot_down.values())
        max_hi = max(max_high.values())
        max_tp = max(max_top.values())

        # Also compute max path length in the DAG
        max_depth = {c: 0 for c in bad_set}
        for c in topo_order:
            for s in adj[c]:
                max_depth[s] = max(max_depth[s], max_depth[c] + 1)

        max_path = max(max_depth.values())

        print(f"\n  n={nv}: {len(bad_set)} bad, max_path={max_path}")
        print(f"    Max anomalous firings on any path: {max_total}")
        print(f"      T_bot(0,0,0)→1: {max_bu}")
        print(f"      T_bot(1,1,2)→0: {max_bd}")
        print(f"      T_high(1,1,1)→2: {max_hi}")
        print(f"      T_top(2,0,0)→1: {max_tp}")

    # ── Detailed: what happens between consecutive same-type firings? ──
    print("\n\n" + "=" * 70)
    print("BETWEEN-FIRING ANALYSIS")
    print("=" * 70)
    print("For each pair of consecutive same-type anomalous firings on a path,")
    print("check what quantity decreases.\n")

    for nv in [5, 6, 7]:
        prod = 4 * 3 ** (nv - 2)
        if prod > 30000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        # Build adjacency
        adj = {c: [] for c in bad_set}
        edge_info = {}
        for c in bad_set:
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append(succ)
                        cls = classify(Li, Si, Ri, out)
                        edge_info[(c, succ)] = (cls, i, delta_fc(Li, Si, Ri, out))

        # Find all configs where each anomalous type fires
        bot_up_srcs = []  # configs where T_bot(0,0,0)→1 fires (bad→bad)
        for c in bad_set:
            if c[n-1] == 0 and c[0] == 0 and c[1] == 0:
                lst = list(c); lst[0] = 1; succ = tuple(lst)
                if succ in bad_set:
                    bot_up_srcs.append((c, succ))

        # For a few bot_up_srcs, BFS forward to find the NEXT bot_up firing
        print(f"  n={nv}: {len(bot_up_srcs)} T_bot(0,0,0)→1 sources")
        checked = 0
        results = {'fc_dec': 0, 'fc_same': 0, 'fc_inc': 0,
                   'psi_dec': 0, 'psi_same': 0, 'psi_inc': 0,
                   'sum_dec': 0, 'sum_same': 0, 'sum_inc': 0}

        for src, after_fire in bot_up_srcs:
            # BFS from after_fire to find configs where T_bot(0,0,0)→1 fires again
            visited = {after_fire}
            queue = deque([after_fire])
            found_next = []
            while queue:
                cur = queue.popleft()
                for s in adj[cur]:
                    if s not in visited:
                        visited.add(s)
                        # Check if T_bot(0,0,0)→1 fires at s
                        if s[n-1] == 0 and s[0] == 0 and s[1] == 0:
                            lst2 = list(s); lst2[0] = 1; nxt = tuple(lst2)
                            if nxt in bad_set:
                                found_next.append(s)
                                continue  # don't BFS further from here
                        queue.append(s)

            for nxt_src in found_next:
                dfc = sum(1 for j in range(n) if nxt_src[j] != nxt_src[(j+1)%n]) - \
                      sum(1 for j in range(n) if src[j] != src[(j+1)%n])
                dpsi = psi(nxt_src, n) - psi(src, n)
                dsum = sum(nxt_src) - sum(src)
                if dfc < 0: results['fc_dec'] += 1
                elif dfc == 0: results['fc_same'] += 1
                else: results['fc_inc'] += 1
                if dpsi < 0: results['psi_dec'] += 1
                elif dpsi == 0: results['psi_same'] += 1
                else: results['psi_inc'] += 1
                if dsum < 0: results['sum_dec'] += 1
                elif dsum == 0: results['sum_same'] += 1
                else: results['sum_inc'] += 1

            checked += 1

        total_pairs = results['fc_dec'] + results['fc_same'] + results['fc_inc']
        print(f"    {total_pairs} (src, next_src) pairs for T_bot(0,0,0)→1")
        print(f"    fc: {results['fc_dec']} dec, {results['fc_same']} same, {results['fc_inc']} inc")
        print(f"    Ψ:  {results['psi_dec']} dec, {results['psi_same']} same, {results['psi_inc']} inc")
        print(f"    sum: {results['sum_dec']} dec, {results['sum_same']} same, {results['sum_inc']} inc")

    # ── Check the right-boundary 2-cycle bug ──────────────────────
    print("\n\n" + "=" * 70)
    print("RIGHT-BOUNDARY 2-CYCLE VERIFICATION")
    print("=" * 70)
    print("Checking if T_top(2,1,0) actually outputs 0 (which would create a 2-cycle)")

    # Read T_top table directly
    print(f"\n  T_top table entries with S=1:")
    for (L, S, R), out in sorted(T_top.items()):
        if S == 1:
            cls_name = classify(L, S, R, out) if out != S else "stay"
            print(f"    T_top({L},{S},{R}) = {out}  [{cls_name}]")

    print(f"\n  Specifically: T_top(2,1,0) = {T_top[(2,1,0)]}")
    print(f"  If T_top(2,1,0) = 0, that's copy_R → 2-cycle exists")
    print(f"  If T_top(2,1,0) = 1, that's STAY → no edge, no 2-cycle")

    # If 2-cycle edge exists, verify the bad graph is still DAG
    if T_top[(2,1,0)] == 0:
        print("\n  T_top(2,1,0)=0 → reverse edge EXISTS. 2-cycle is real!")
        print("  But DAG was verified... checking more carefully")
        for nv in [5, 6]:
            ms, fs = build_system(nv)
            n = nv
            result = verify_system(ms, fs)
            good_set = result['good_configs']
            all_configs = list(cartesian(*(range(m) for m in ms)))
            bad_set = set(c for c in all_configs if c not in good_set)
            # Find actual 2-cycles in the bad graph
            real_cycles = 0
            for c in bad_set:
                for i in range(n):
                    Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                    out = fs[i](Li, Si, Ri)
                    if out != Si:
                        lst = list(c); lst[i] = out; succ = tuple(lst)
                        if succ in bad_set:
                            # Check reverse: does succ have an edge to c?
                            for j in range(n):
                                Lj = succ[(j-1)%n]; Sj = succ[j]; Rj = succ[(j+1)%n]
                                outj = fs[j](Lj, Sj, Rj)
                                if outj != Sj:
                                    lst2 = list(succ); lst2[j] = outj; back = tuple(lst2)
                                    if back == c:
                                        real_cycles += 1
            print(f"  n={nv}: {real_cycles} actual 2-cycle pairs (counting both directions)")
    else:
        print("\n  T_top(2,1,0)≠0 → no reverse edge, 2-cycle bug confirmed")


if __name__ == "__main__":
    main()
