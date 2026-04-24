#!/usr/bin/env python3
"""Deep structural analysis of anomalous transitions.

The 5 anomalous entries:
  T_bot(0,0,0)→1: Δfc=+2   (position 0)
  T_bot(1,1,2)→0: Δfc=+1   (position 0)
  T_mid(2,1,1)→0: Δfc=+1   (position i, 2≤i≤n-3)
  T_high(1,1,1)→2: Δfc=+2  (position n-2)
  T_top(2,0,0)→1: Δfc=+1   (position n-1)

Key question: can a cycle in the full transition graph use anomalous edges?
A cycle must have total Δfc = 0, so anomalous increases must be balanced by
copy-neighbor decreases. But can we show the necessary fc-decreasing path
back down is always blocked?

Strategy: for each anomalous transition c→c', study the "return set" —
configs reachable from c' by Δfc≤0 transitions. If c is never in the
return set of c', then no cycle through this anomalous edge exists.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def classify_entry(L, S, R, out):
    if out == S: return "stay"
    if out == L: return "copy_L"
    if out == R: return "copy_R"
    return "anomalous"


def main():
    print("ANOMALOUS TRANSITION STRUCTURE ANALYSIS")
    print("=" * 70)

    for nv in range(5, 11):
        prod = 4 * 3 ** (nv - 2)
        if prod > 100000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        # Build full transition graph and classify edges
        adj_full = {c: [] for c in bad_set}
        adj_leq0 = {c: [] for c in bad_set}
        anomalous_edges = []

        for c in bad_set:
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    dfc = delta_fc(Li, Si, Ri, out)
                    cls = classify_entry(Li, Si, Ri, out)
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        adj_full[c].append(succ)
                        if dfc <= 0:
                            adj_leq0[c].append(succ)
                        if cls == "anomalous":
                            anomalous_edges.append((c, succ, i, dfc, cls))

        print(f"\nn={nv}: {len(bad_set)} bad configs, "
              f"{len(anomalous_edges)} anomalous edges")

        # For each anomalous edge c→c':
        # Can c be reached from c' using only Δfc≤0 edges?
        # (If yes, there's a potential cycle through this anomalous edge)
        reachable_count = 0
        cycle_edges = []
        for c, cp, mv, dfc, cls in anomalous_edges:
            # BFS from c' using Δfc≤0 edges
            visited = set()
            queue = deque([cp])
            visited.add(cp)
            found = False
            while queue:
                cur = queue.popleft()
                if cur == c:
                    found = True
                    break
                for s in adj_leq0[cur]:
                    if s not in visited:
                        visited.add(s)
                        queue.append(s)
            if found:
                reachable_count += 1
                cycle_edges.append((c, cp, mv, dfc))

        print(f"  Anomalous edges where source reachable from target "
              f"via Δfc≤0: {reachable_count}/{len(anomalous_edges)}")

        if cycle_edges and nv <= 7:
            for c, cp, mv, dfc in cycle_edges[:5]:
                print(f"    {c} →[P{mv}]→ {cp} (Δfc={dfc:+d})")

        # If reachable_count > 0, the Δfc≤0 DAG proof alone isn't enough.
        # But the FULL graph is still a DAG. So something else prevents cycles.
        # Let's check: for those "reachable" pairs, does the return path
        # go through configs at fc < fc(c)? If so, the cycle would need
        # ANOTHER anomalous edge to climb back up.

        if reachable_count > 0:
            # For each such pair, find the fc values along the return path
            print(f"\n  Analyzing return paths for reachable anomalous edges:")
            for c, cp, mv, dfc in cycle_edges[:3]:
                fc_c = sum(1 for j in range(n) if c[j] != c[(j+1)%n])
                fc_cp = sum(1 for j in range(n) if cp[j] != cp[(j+1)%n])
                # BFS from c' to c, tracking min fc along path
                parent = {cp: None}
                queue = deque([cp])
                found_path = False
                while queue:
                    cur = queue.popleft()
                    if cur == c:
                        found_path = True
                        break
                    for s in adj_leq0[cur]:
                        if s not in parent:
                            parent[s] = cur
                            queue.append(s)
                if found_path:
                    # Trace path
                    path = []
                    cur = c
                    while cur is not None:
                        path.append(cur)
                        cur = parent[cur]
                    path.reverse()
                    fc_along = [sum(1 for j in range(n) if p[j] != p[(j+1)%n])
                                for p in path]
                    min_fc = min(fc_along)
                    print(f"    {c}→{cp}: fc={fc_c}→{fc_cp}, "
                          f"return path len={len(path)}, "
                          f"fc range=[{min_fc}..{max(fc_along)}]")

    # Now check: among the full transition edges, what fraction are anomalous?
    # And what is the fc distribution of anomalous transitions?
    print("\n\nANOMALOUS EDGE fc DISTRIBUTION")
    print("-" * 60)
    for nv in range(5, 11):
        prod = 4 * 3 ** (nv - 2)
        if prod > 100000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        fc_dist = {}
        for c in bad_set:
            fc_c = sum(1 for j in range(n) if c[j] != c[(j+1)%n])
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    cls = classify_entry(Li, Si, Ri, out)
                    if cls == "anomalous":
                        lst = list(c); lst[i] = out; succ = tuple(lst)
                        if succ in bad_set:
                            fc_dist[fc_c] = fc_dist.get(fc_c, 0) + 1

        print(f"  n={nv}: anomalous edges by source fc: {dict(sorted(fc_dist.items()))}")

    # KEY INSIGHT: check if anomalous transitions only fire from
    # configs with LOW fc (close to good configs).
    # If they only fire from fc ≤ k, and the resulting config has fc ≤ k+2,
    # then the "climb" is bounded.

    print("\n\nANOMALOUS SOURCE/TARGET fc RANGES")
    print("-" * 60)
    for nv in range(5, 11):
        prod = 4 * 3 ** (nv - 2)
        if prod > 100000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        max_src_fc = 0
        max_tgt_fc = 0
        max_fc_overall = max(sum(1 for j in range(n) if c[j] != c[(j+1)%n])
                            for c in bad_set)
        for c in bad_set:
            fc_c = sum(1 for j in range(n) if c[j] != c[(j+1)%n])
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    cls = classify_entry(Li, Si, Ri, out)
                    if cls == "anomalous":
                        lst = list(c); lst[i] = out; succ = tuple(lst)
                        if succ in bad_set:
                            fc_s = sum(1 for j in range(n)
                                      if succ[j] != succ[(j+1)%n])
                            max_src_fc = max(max_src_fc, fc_c)
                            max_tgt_fc = max(max_tgt_fc, fc_s)

        print(f"  n={nv}: max_fc={max_fc_overall}, "
              f"anomalous src max_fc={max_src_fc}, "
              f"anomalous tgt max_fc={max_tgt_fc}")


if __name__ == "__main__":
    main()
