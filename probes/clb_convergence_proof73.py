#!/usr/bin/env python3
"""
CONVERGENCE PROOF 73: Joint (Δfc, Δrank_up) distribution on jdz edges
======================================================================
KEY QUESTION: On Δfc < 0 jdz edges, does rank_up ever increase?
If Δrank_up ≤ 0 for |Δfc| ≤ 3, then Φ = fc + 3·rank_up is strictly
decreasing on ALL jdz edges → jdz is DAG → convergence proved.

Also check:
- Exact joint distribution of (Δfc, Δrank_up)
- Whether Φ = fc + α·rank_up works for any α
- For any violations: detailed analysis of the offending edges
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter, deque

def delta_fc_val(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])

def build_excursion_graph(n_val):
    ms, fs = build_system(n_val)
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)
    anom_edges = []
    dfc_le0_adj = defaultdict(list)
    for c in bad_list:
        for i in range(n_val):
            L = c[(i - 1) % n_val]
            S = c[i]
            R = c[(i + 1) % n_val]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c)
                lst[i] = out
                succ = tuple(lst)
                if succ in bad_set:
                    dfc = delta_fc_val(L, S, R, out)
                    if dfc <= 0:
                        dfc_le0_adj[c].append(succ)
                    if out != L and out != R:
                        anom_edges.append((c, succ, i, dfc))
    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_target_map = defaultdict(list)
    for c, succ, i, dfc in anom_edges:
        anom_target_map[succ].append(c)
    exc_edges = set()
    for b in set(s for _, s, _, _ in anom_edges):
        visited = {b}
        queue = [b]
        head = 0
        while head < len(queue):
            node = queue[head]
            head += 1
            if node in anom_sources:
                for src in anom_target_map.get(b, []):
                    exc_edges.add((src, node))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append(nxt)
    return list(exc_edges), ms

def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def int_j_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 13):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        jdz = list(set((u, v) for u, v in exc_edges
                       if int_21(v, n) - int_21(u, n) == 0
                       and int_j_20(v, n) - int_j_20(u, n) == 0))

        if not jdz:
            print(f"n={n}: no jdz edges")
            continue

        # Build Δfc≥0 subgraph and compute rank_up
        up_adj = defaultdict(list)
        up_nodes = set()
        for u, v in jdz:
            if fc(v, n) >= fc(u, n):
                up_adj[u].append(v)
                up_nodes.add(u)
                up_nodes.add(v)

        # Topological sort of Δfc≥0 subgraph
        in_deg = defaultdict(int)
        for u in up_nodes:
            for v in up_adj[u]:
                in_deg[v] += 1
        q = deque([u for u in up_nodes if in_deg[u] == 0])
        topo = []
        while q:
            node = q.popleft()
            topo.append(node)
            for nxt in up_adj[node]:
                in_deg[nxt] -= 1
                if in_deg[nxt] == 0:
                    q.append(nxt)
        assert len(topo) == len(up_nodes), f"Δfc≥0 not DAG at n={n}!"

        rank_up = {}
        for c in reversed(topo):
            rank_up[c] = max((rank_up[s] + 1 for s in up_adj[c]), default=0)
        max_rank = max(rank_up.values()) if rank_up else 0

        # For configs NOT in up_nodes: rank_up = 0 (they have no Δfc≥0 edges)
        # Actually, they're not in the Δfc≥0 subgraph at all. Define rank_up = 0 for them.

        print(f"\n{'=' * 70}", flush=True)
        print(f"n={n}: {len(jdz)} jdz edges, Δfc≥0 rank={max_rank} ({time.time()-t0:.1f}s)", flush=True)
        print(f"{'=' * 70}", flush=True)

        # === Joint (Δfc, Δrank_up) distribution ===
        joint = Counter()
        for u, v in jdz:
            dfc = fc(v, n) - fc(u, n)
            ru = rank_up.get(u, 0)
            rv = rank_up.get(v, 0)
            dr = rv - ru
            joint[(dfc, dr)] += 1

        print(f"\n  Joint (Δfc, Δrank_up) distribution:", flush=True)
        dfc_vals = sorted(set(d for d, _ in joint.keys()))
        dr_vals = sorted(set(d for _, d in joint.keys()))

        # Header
        header = f"{'':>12s}" + "".join(f"Δr={dr:+d}".rjust(9) for dr in dr_vals)
        print(f"  {header}", flush=True)
        for dfc in dfc_vals:
            row = f"  Δfc={dfc:+d}".ljust(12)
            for dr in dr_vals:
                cnt = joint.get((dfc, dr), 0)
                row += f"{cnt:>9d}" if cnt > 0 else f"{'·':>9s}"
                # row += f"{'·' if cnt == 0 else cnt:>9}"
            print(f"  {row}", flush=True)

        # === Key question: on Δfc < 0 edges, max Δrank_up ===
        print(f"\n  Max Δrank_up by Δfc:", flush=True)
        for dfc in sorted(dfc_vals):
            max_dr = max(dr for (d, dr) in joint.keys() if d == dfc)
            total = sum(v for (d, dr), v in joint.items() if d == dfc)
            print(f"    Δfc={dfc:+d}: max Δrank_up = {max_dr:+d} ({total} edges)", flush=True)

        # === Test Φ = fc + α·rank_up for various α ===
        print(f"\n  Potential Φ = fc + α·rank_up tests:", flush=True)
        for alpha_num, alpha_den in [(3,1), (4,1), (5,1), (7,2), (5,2), (3,2)]:
            # Φ = fc + (alpha_num/alpha_den) * rank_up
            # ΔΦ = Δfc + (alpha_num/alpha_den) * Δrank_up
            # Violations: ΔΦ ≥ 0
            viol = 0
            max_dphi = -float('inf')
            for u, v in jdz:
                dfc = fc(v, n) - fc(u, n)
                dr = rank_up.get(v, 0) - rank_up.get(u, 0)
                dphi = dfc * alpha_den + alpha_num * dr  # scaled by alpha_den
                if dphi >= 0:
                    viol += 1
                max_dphi = max(max_dphi, dphi / alpha_den)
            alpha_str = f"{alpha_num}/{alpha_den}" if alpha_den > 1 else f"{alpha_num}"
            pct = 100 * viol / len(jdz)
            print(f"    α={alpha_str}: {viol}/{len(jdz)} violations ({pct:.1f}%), max ΔΦ={max_dphi:.2f}", flush=True)

        # === Detailed analysis of Δfc=-1, Δrank_up>0 edges (if any) ===
        bad_edges = [(u, v) for u, v in jdz
                     if fc(v, n) - fc(u, n) == -1
                     and rank_up.get(v, 0) > rank_up.get(u, 0)]
        if bad_edges:
            print(f"\n  WARNING: {len(bad_edges)} edges with Δfc=-1, Δrank_up>0!", flush=True)
            for u, v in bad_edges[:5]:
                ru = rank_up.get(u, 0)
                rv = rank_up.get(v, 0)
                bdry_u = (u[0], u[1], u[n-2], u[n-1])
                bdry_v = (v[0], v[1], v[n-2], v[n-1])
                # What positions changed?
                changed = [j for j in range(n) if u[j] != v[j]]
                print(f"    {bdry_u}→{bdry_v}: rank {ru}→{rv}, fc {fc(u,n)}→{fc(v,n)}, "
                      f"changed positions: {changed}", flush=True)
        else:
            print(f"\n  ✓ No edges with Δfc=-1 AND Δrank_up>0", flush=True)

        # More general: Δfc in {-1,-2,-3} with Δrank_up > 0
        for dfc_test in [-1, -2, -3]:
            bad = [(u, v) for u, v in jdz
                   if fc(v, n) - fc(u, n) == dfc_test
                   and rank_up.get(v, 0) > rank_up.get(u, 0)]
            if bad:
                max_dr = max(rank_up.get(v, 0) - rank_up.get(u, 0) for u, v in bad)
                print(f"  Δfc={dfc_test}: {len(bad)} edges with Δrank_up>0 (max Δrank_up={max_dr})", flush=True)

        # === Check: is Φ = fc + 3·rank_up strictly decreasing? ===
        # For Δfc ≥ 0: ΔΦ = Δfc + 3·Δrank_up. Δrank_up ≤ -1, Δfc ≤ 2. Max: 2-3=-1. ✓
        # For Δfc < 0: ΔΦ = Δfc + 3·Δrank_up. Need 3·Δrank_up < |Δfc|.
        phi3_viol = 0
        phi3_worst = []
        for u, v in jdz:
            dfc = fc(v, n) - fc(u, n)
            dr = rank_up.get(v, 0) - rank_up.get(u, 0)
            dphi = dfc + 3 * dr
            if dphi >= 0:
                phi3_viol += 1
                phi3_worst.append((dphi, dfc, dr, u, v))

        print(f"\n  Φ = fc + 3·rank_up: {phi3_viol}/{len(jdz)} violations", flush=True)
        if phi3_worst:
            phi3_worst.sort(reverse=True)
            print(f"  Worst violations:", flush=True)
            for dphi, dfc, dr, u, v in phi3_worst[:10]:
                bdry_u = (u[0], u[1], u[n-2], u[n-1])
                bdry_v = (v[0], v[1], v[n-2], v[n-1])
                print(f"    ΔΦ={dphi:+d}, Δfc={dfc:+d}, Δr={dr:+d}: {bdry_u}→{bdry_v} "
                      f"fc={fc(u,n)}→{fc(v,n)}, rank={rank_up.get(u,0)}→{rank_up.get(v,0)}", flush=True)

        elapsed = time.time() - t0
        print(f"\n  Time: {elapsed:.1f}s", flush=True)

if __name__ == '__main__':
    main()
