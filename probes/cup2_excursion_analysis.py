#!/usr/bin/env python3
"""Analyze excursion structure for multi-level induction.

For each fc level f, consider configs at fc=f. Among these, Δfc=0
transitions form a DAG (by Ψ potential). A hypothetical cycle at level f
must excurse below f (via Δfc<0) and return (via anomalous Δfc>0).

Key claim for induction: at each fc level f, the Ψ at re-entry is always
lower than Ψ at exit. If true, each level can be visited only finitely
many times → no cycle.

Also: check if anomalous edges have a special relationship with the
topological order of the full DAG.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from cup2_psi_proof import psi, delta_fc
from itertools import product as cartesian
from collections import deque, defaultdict


def classify_entry(L, S, R, out):
    if out == S: return "stay"
    if out == L: return "copy_L"
    if out == R: return "copy_R"
    return "anomalous"


def compute_topo_depth(adj, nodes):
    """Compute longest path from each node to a sink (no successors in nodes)."""
    # First compute in-degree for reverse topo sort
    # Actually, compute depth = longest path to any sink
    depth = {}
    # Reverse graph
    rev_adj = {c: [] for c in nodes}
    for c in nodes:
        for s in adj.get(c, []):
            if s in nodes:
                rev_adj[s].append(c)

    # Topo sort by Kahn's, computing depth
    out_deg = {c: 0 for c in nodes}
    for c in nodes:
        for s in adj.get(c, []):
            if s in nodes:
                out_deg[c] += 1

    queue = deque(c for c in nodes if out_deg[c] == 0)
    for c in queue:
        depth[c] = 0

    while queue:
        c = queue.popleft()
        for p in rev_adj[c]:
            out_deg[p] -= 1
            if p not in depth:
                depth[p] = 0
            depth[p] = max(depth[p], depth[c] + 1)
            if out_deg[p] == 0:
                queue.append(p)

    return depth


def main():
    print("EXCURSION ANALYSIS FOR MULTI-LEVEL INDUCTION")
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

        # Build full adjacency and classify
        adj_full = {c: [] for c in bad_set}
        adj_leq0 = {c: [] for c in bad_set}
        edge_info = []  # (src, tgt, pos, dfc, cls)

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
                        edge_info.append((c, succ, i, dfc, cls))

        # Compute fc for each config
        fc = {c: sum(1 for j in range(n) if c[j] != c[(j+1)%n]) for c in bad_set}
        max_fc = max(fc.values())

        # Compute topological depth in full DAG
        topo_depth = compute_topo_depth(adj_full, bad_set)

        # For each anomalous edge c→c', check relationship between
        # topo_depth in full DAG
        print(f"\nn={nv}: max_fc={max_fc}, {len(bad_set)} bad configs")

        anom_depth_ok = 0
        anom_depth_bad = 0
        for c, cp, pos, dfc, cls in edge_info:
            if cls == "anomalous":
                if topo_depth[c] > topo_depth[cp]:
                    anom_depth_ok += 1
                else:
                    anom_depth_bad += 1

        print(f"  Anomalous edges: topo_depth decreasing={anom_depth_ok}, "
              f"non-decreasing={anom_depth_bad}")

        # For each fc level f, find all anomalous entries INTO level f
        # (target at fc=f, source at fc=f-1 or f-2)
        # and all exits FROM level f (Δfc<0 edges from fc=f to fc<f).
        # Check: Ψ at entry ≤ Ψ at exit for "paired" excursions.

        # More precisely: for each pair (exit config a, re-entry config b)
        # at the same fc level f, where there's a path a→...→b in the full
        # graph going through fc<f configs, check Ψ(b) < Ψ(a).

        # This is expensive to check directly. Instead, let's check a simpler
        # property: for anomalous edges going TO fc=f, is the Ψ at target
        # always less than the max Ψ at fc=f?

        for f in range(2, max_fc + 1):
            configs_at_f = [c for c in bad_set if fc[c] == f]
            if not configs_at_f:
                continue
            max_psi_f = max(psi(c, n) for c in configs_at_f)

            # Anomalous entries into level f
            anom_into_f = [(c, cp) for c, cp, pos, dfc, cls in edge_info
                           if cls == "anomalous" and fc[cp] == f]
            if anom_into_f:
                psi_at_entry = [psi(cp, n) for c, cp in anom_into_f]
                max_psi_entry = max(psi_at_entry) if psi_at_entry else 0
                # Check Ψ at exits from level f
                exits_from_f = [(c, cp) for c, cp, pos, dfc, cls in edge_info
                                if dfc < 0 and fc[c] == f and c in bad_set]
                if exits_from_f:
                    psi_at_exit = [psi(c, n) for c, cp in exits_from_f]
                    min_psi_exit = min(psi_at_exit)
                    # For induction to work: max entry Ψ < min exit Ψ
                    # (then entries always come "after" exits in Ψ order)
                    if nv <= 7:
                        print(f"  fc={f}: max_psi_entry={max_psi_entry}, "
                              f"min_psi_exit={min_psi_exit}, "
                              f"separated={'Y' if max_psi_entry < min_psi_exit else 'N'}")

    # Try a different check: for the full DAG, does a "level-respecting"
    # topological order exist where anomalous edges go in the same direction?
    print("\n\nFULL DAG TOPOLOGICAL DEPTH vs (fc, Ψ)")
    print("-" * 60)
    for nv in range(5, 9):
        prod = 4 * 3 ** (nv - 2)
        if prod > 30000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        adj_full = {c: [] for c in bad_set}
        for c in bad_set:
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        adj_full[c].append(succ)

        topo = compute_topo_depth(adj_full, bad_set)

        # Check if topo_depth can be expressed as f(fc, Ψ)
        # Group configs by (fc, Ψ) and check if topo_depth is determined
        from collections import defaultdict
        groups = defaultdict(set)
        for c in bad_set:
            key = (sum(1 for j in range(n) if c[j] != c[(j+1)%n]), psi(c, n))
            groups[key].add(topo[c])

        multi_depth = sum(1 for v in groups.values() if len(v) > 1)
        max_spread = max(max(v) - min(v) for v in groups.values()) if groups else 0
        print(f"  n={nv}: {len(groups)} distinct (fc,Ψ) pairs, "
              f"{multi_depth} have multiple topo depths, max spread={max_spread}")

        # Is there a simple third observable that disambiguates?
        # Try sum(c)
        groups3 = defaultdict(set)
        for c in bad_set:
            key = (sum(1 for j in range(n) if c[j] != c[(j+1)%n]),
                   psi(c, n), sum(c))
            groups3[key].add(topo[c])
        multi3 = sum(1 for v in groups3.values() if len(v) > 1)
        max_s3 = max(max(v) - min(v) for v in groups3.values()) if groups3 else 0
        print(f"         with sum: {multi3} have multiple depths, spread={max_s3}")


if __name__ == "__main__":
    main()
