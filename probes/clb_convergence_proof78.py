#!/usr/bin/env python3
"""
CONVERGENCE PROOF 78: Structural analysis of Δfc<0 jdz edges
=============================================================
Focus on what CHANGES on the descending edges (Δfc<0) in jdz.
These are the hard edges — fc drops but rank_up can jump.

For each Δfc<0 jdz edge u→v:
1. Which anomalous entry generated it at u?
2. How do boundary values change?
3. How does the interior change (positions, values)?
4. Is there a monotone quantity that decreases EVEN on these edges?

Also: detailed rank analysis per sub-component for small n.
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

def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def int_j_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def int_j_21(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def int_20(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def classify_anom_entry(pos, L, S, R, out, n):
    if pos == 0 and (L, S, R, out) == (0, 0, 0, 1):
        return 'E1:bot(0,0,0)→1'
    elif pos == 0 and (L, S, R, out) == (1, 1, 2, 0):
        return 'E2:bot(1,1,2)→0'
    elif 2 <= pos <= n - 3 and (L, S, R, out) == (2, 1, 1, 0):
        return f'E3:mid(2,1,1)→0@{pos}'
    elif pos == n - 2 and (L, S, R, out) == (1, 1, 1, 2):
        return 'E4:high(1,1,1)→2'
    elif pos == n - 1 and (L, S, R, out) == (2, 0, 0, 1):
        return 'E5:top(2,0,0)→1'
    else:
        return f'?:pos{pos}({L},{S},{R})→{out}'

def build_jdz_with_entry(n_val):
    """Build jdz graph with anomalous entry info for each edge."""
    ms, fs = build_system(n_val)
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)
    n = n_val

    anom_edges = []
    dfc_le0_adj = defaultdict(list)
    for c in bad_list:
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
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
    anom_step_info = {}
    for c, succ, i, dfc in anom_edges:
        anom_target_map[succ].append(c)
        anom_step_info[(c, succ)] = (i, c[(i-1)%n], c[i], c[(i+1)%n], succ[i])

    jdz_with_info = []
    seen = set()
    for b in set(s for _, s, _, _ in anom_edges):
        visited = {b}
        queue = [b]
        head = 0
        while head < len(queue):
            node = queue[head]
            head += 1
            if node in anom_sources:
                for src in anom_target_map.get(b, []):
                    if (src, node) not in seen:
                        # Check jdz invariants
                        if (int_21(node, n) - int_21(src, n) == 0 and
                            int_j_20(node, n) - int_j_20(src, n) == 0):
                            seen.add((src, node))
                            info = anom_step_info.get((src, b))
                            jdz_with_info.append((src, node, info))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append(nxt)

    return jdz_with_info, ms, fs


def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(7, 12):
        t0 = time.time()
        jdz_with_info, ms, fs = build_jdz_with_entry(n_val)
        n = n_val

        if not jdz_with_info:
            print(f"n={n}: no jdz edges")
            continue

        # Build adjacency
        jdz_adj = defaultdict(list)
        jdz_nodes = set()
        edge_info = {}
        for u, v, info in jdz_with_info:
            jdz_adj[u].append(v)
            jdz_nodes.add(u)
            jdz_nodes.add(v)
            if info:
                pos, L, S, R, out = info
                edge_info[(u, v)] = classify_anom_entry(pos, L, S, R, out, n)

        # Compute full DAG rank
        in_deg = defaultdict(int)
        for u, v, _ in jdz_with_info:
            in_deg[v] += 1
        q = deque([u for u in jdz_nodes if in_deg[u] == 0])
        topo = []
        while q:
            node = q.popleft()
            topo.append(node)
            for nxt in jdz_adj[node]:
                in_deg[nxt] -= 1
                if in_deg[nxt] == 0:
                    q.append(nxt)
        assert len(topo) == len(jdz_nodes), f"jdz NOT DAG at n={n}!"

        full_rank = {}
        for c in reversed(topo):
            full_rank[c] = max((full_rank[s] + 1 for s in jdz_adj[c]), default=0)
        max_full_rank = max(full_rank.values())

        # Compute rank_up (Δfc≥0 subgraph rank)
        up_adj = defaultdict(list)
        up_nodes = set()
        for u, v, _ in jdz_with_info:
            if fc(v, n) >= fc(u, n):
                up_adj[u].append(v)
                up_nodes.add(u)
                up_nodes.add(v)
        in_deg_up = defaultdict(int)
        for u in up_nodes:
            for v in up_adj[u]:
                in_deg_up[v] += 1
        q = deque([u for u in up_nodes if in_deg_up[u] == 0])
        topo_up = []
        while q:
            node = q.popleft()
            topo_up.append(node)
            for nxt in up_adj[node]:
                in_deg_up[nxt] -= 1
                if in_deg_up[nxt] == 0:
                    q.append(nxt)
        rank_up = {}
        for c in reversed(topo_up):
            rank_up[c] = max((rank_up[s] + 1 for s in up_adj[c]), default=0)

        # Separate edges by Δfc sign
        fc_neg_edges = [(u, v) for u, v, _ in jdz_with_info if fc(v, n) < fc(u, n)]
        fc_zero_edges = [(u, v) for u, v, _ in jdz_with_info if fc(v, n) == fc(u, n)]
        fc_pos_edges = [(u, v) for u, v, _ in jdz_with_info if fc(v, n) > fc(u, n)]

        print(f"\n{'=' * 70}", flush=True)
        print(f"n={n}: {len(jdz_with_info)} jdz edges, DAG rank={max_full_rank} "
              f"({time.time()-t0:.1f}s)", flush=True)
        print(f"  Δfc<0: {len(fc_neg_edges)}, Δfc=0: {len(fc_zero_edges)}, "
              f"Δfc>0: {len(fc_pos_edges)}", flush=True)

        # === 1. Entry types on Δfc<0 edges ===
        print(f"\n  Entry types on Δfc<0 jdz edges:", flush=True)
        entry_counts = Counter()
        for u, v in fc_neg_edges:
            entry = edge_info.get((u, v), '?')
            entry_counts[entry] += 1
        for entry, cnt in entry_counts.most_common(10):
            print(f"    {entry}: {cnt}", flush=True)

        # === 2. Boundary transitions on Δfc<0 edges ===
        print(f"\n  Boundary transitions on Δfc<0 edges:", flush=True)
        bdry_trans = Counter()
        for u, v in fc_neg_edges:
            bu = (u[0], u[1], u[n-2], u[n-1])
            bv = (v[0], v[1], v[n-2], v[n-1])
            bdry_trans[(bu, bv)] += 1
        for (bu, bv), cnt in bdry_trans.most_common(10):
            print(f"    {bu} → {bv}: {cnt}", flush=True)

        # === 3. Δ(full_rank) on Δfc<0 edges ===
        print(f"\n  Δ(full_rank) on Δfc<0 edges:", flush=True)
        dr_dist = Counter()
        for u, v in fc_neg_edges:
            dr = full_rank[v] - full_rank[u]
            dr_dist[dr] += 1
        # Should ALL be negative (since jdz is DAG)
        print(f"    Distribution: {dict(sorted(dr_dist.items()))}", flush=True)
        min_dr = min(dr_dist.keys())
        max_dr = max(dr_dist.keys())
        print(f"    Range: [{min_dr}, {max_dr}]", flush=True)

        # === 4. Search for monotone quantity on ALL jdz edges ===
        # Test: rank decreases by at least 1 on every edge (this is guaranteed)
        # But can we express rank as a function of (fc, interior_pattern)?

        # Test many candidate potentials
        def boundary_sum(c):
            return c[0] + c[1] + c[n-2] + c[n-1]

        def interior_lex(c):
            """Interpret interior as a number in base 3."""
            val = 0
            for j in range(2, n - 2):
                val = val * 3 + c[j]
            return val

        def interior_rev_lex(c):
            """Interpret reversed interior as a number in base 3."""
            val = 0
            for j in range(n - 3, 1, -1):
                val = val * 3 + c[j]
            return val

        def rightmost_2(c):
            for j in range(n - 3, 1, -1):
                if c[j] == 2:
                    return j
            return 0

        def leftmost_0(c):
            for j in range(2, n - 2):
                if c[j] == 0:
                    return j
            return n

        def config_as_int(c):
            """Full config as integer."""
            val = 0
            for j in range(n):
                val = val * 3 + c[j]
            return val

        candidates = {
            'fc': lambda c: fc(c, n),
            '-fc': lambda c: -fc(c, n),
            'rank_up': lambda c: rank_up.get(c, 0),
            'interior_lex': interior_lex,
            '-interior_lex': lambda c: -interior_lex(c),
            'interior_rev_lex': interior_rev_lex,
            '-interior_rev_lex': lambda c: -interior_rev_lex(c),
            'config_int': config_as_int,
            '-config_int': lambda c: -config_as_int(c),
            'bdry_sum': boundary_sum,
            '-bdry_sum': lambda c: -boundary_sum(c),
            'rightmost_2': lambda c: rightmost_2(c),
            '-rightmost_2': lambda c: -rightmost_2(c),
            'leftmost_0': lambda c: leftmost_0(c),
            '-leftmost_0': lambda c: -leftmost_0(c),
            '4fc+rank_up': lambda c: 4*fc(c,n) + rank_up.get(c, 0),
            '-4fc-rank_up': lambda c: -4*fc(c,n) - rank_up.get(c, 0),
            'fc*10+rank_up': lambda c: fc(c,n)*10 + rank_up.get(c, 0),
        }

        print(f"\n  Monotonicity tests (strict decrease on ALL jdz edges):", flush=True)
        for cname, cfunc in candidates.items():
            viol = sum(1 for u, v, _ in jdz_with_info if cfunc(v) >= cfunc(u))
            pct = 100 * viol / len(jdz_with_info)
            if pct < 40:
                print(f"    {cname:25s}: {viol}/{len(jdz_with_info)} violations ({pct:.1f}%)",
                      flush=True)

        # === 5. For dominant sub-component at n=7,8: exact rank function ===
        if n_val <= 9:
            # Group by sub-component
            comp = defaultdict(set)
            comp_edges = defaultdict(list)
            for u, v, info in jdz_with_info:
                key = (int_21(u, n), int_j_20(u, n), int_j_21(u, n), int_20(u, n))
                comp[key].add(u)
                comp[key].add(v)
                comp_edges[key].append((u, v))

            dom_key = max(comp.keys(), key=lambda k: len(comp_edges[k]))
            dom_nodes = comp[dom_key]
            dom_edges = comp_edges[dom_key]

            print(f"\n  Dominant sub-component {dom_key}: "
                  f"{len(dom_nodes)} nodes, {len(dom_edges)} edges", flush=True)

            # fc distribution within dominant component
            fc_dist = Counter(fc(c, n) for c in dom_nodes)
            print(f"  fc distribution: {dict(sorted(fc_dist.items()))}", flush=True)

            # At each fc level: try to find ordering
            fc_levels = sorted(set(fc(c, n) for c in dom_nodes))
            for f_level in fc_levels:
                level_nodes = [c for c in dom_nodes if fc(c, n) == f_level]
                level_edges = [(u, v) for u, v in dom_edges
                               if fc(u, n) == f_level and fc(v, n) == f_level]
                if level_edges:
                    # Check DAG within this fc level
                    la = defaultdict(list)
                    for u, v in level_edges:
                        la[u].append(v)
                    lid = defaultdict(int)
                    for u, v in level_edges:
                        lid[v] += 1
                    lq = deque([u for u in level_nodes if lid[u] == 0])
                    lt = []
                    while lq:
                        node = lq.popleft()
                        lt.append(node)
                        for nxt in la[node]:
                            lid[nxt] -= 1
                            if lid[nxt] == 0:
                                lq.append(nxt)
                    is_level_dag = len(lt) == len(level_nodes)
                    if is_level_dag:
                        lr = {}
                        for c in reversed(lt):
                            lr[c] = max((lr[s] + 1 for s in la[c]), default=0)
                        max_lr = max(lr.values()) if lr else 0
                    else:
                        max_lr = -1
                    print(f"    fc={f_level}: {len(level_nodes)} nodes, "
                          f"{len(level_edges)} same-fc edges, DAG={is_level_dag}, "
                          f"rank={max_lr}", flush=True)

        # === 6. KEY: On Δfc<0 edges, does fc_drop > rank_up_gain? ===
        # If |Δfc| > Δrank_up always, then Φ = fc + rank_up strictly decreases
        print(f"\n  On Δfc<0 edges: |Δfc| vs Δrank_up:", flush=True)
        joint = Counter()
        violations = []
        for u, v in fc_neg_edges:
            dfc = fc(v, n) - fc(u, n)  # negative
            dr = rank_up.get(v, 0) - rank_up.get(u, 0)
            joint[(dfc, dr)] += 1
            if abs(dfc) <= dr:  # bad: rank gain exceeds fc drop
                violations.append((u, v, dfc, dr))

        for (dfc, dr) in sorted(joint.keys()):
            cnt = joint[(dfc, dr)]
            bad = "!!!" if abs(dfc) <= dr else ""
            print(f"    Δfc={dfc:+d}, Δrank_up={dr:+d}: {cnt} {bad}", flush=True)

        if violations:
            print(f"\n  VIOLATIONS (|Δfc| ≤ Δrank_up): {len(violations)}", flush=True)
            for u, v, dfc, dr in violations[:5]:
                bu = (u[0], u[1], u[n-2], u[n-1])
                bv = (v[0], v[1], v[n-2], v[n-1])
                entry = edge_info.get((u, v), '?')
                print(f"    {bu}→{bv}: Δfc={dfc}, Δr_up={dr}, entry={entry}, "
                      f"full_rank: {full_rank[u]}→{full_rank[v]}", flush=True)
        else:
            print(f"\n  ✓ |Δfc| > Δrank_up on ALL Δfc<0 edges!", flush=True)

        # === 7. Test Φ = fc + rank_up: does it strictly decrease? ===
        phi_viol = 0
        phi_detail = Counter()
        for u, v, _ in jdz_with_info:
            pu = fc(u, n) + rank_up.get(u, 0)
            pv = fc(v, n) + rank_up.get(v, 0)
            dp = pv - pu
            if dp >= 0:
                phi_viol += 1
                phi_detail[dp] += 1

        print(f"\n  Φ = fc + rank_up: {phi_viol}/{len(jdz_with_info)} violations", flush=True)
        if phi_viol > 0:
            print(f"  Violation distribution: {dict(sorted(phi_detail.items()))}", flush=True)

        # === 8. Test Φ = n*fc + rank_up ===
        for mult in [2, 3, 4, 5, n-3]:
            phi_viol = 0
            for u, v, _ in jdz_with_info:
                pu = mult * fc(u, n) + rank_up.get(u, 0)
                pv = mult * fc(v, n) + rank_up.get(v, 0)
                if pv >= pu:
                    phi_viol += 1
            pct = 100 * phi_viol / len(jdz_with_info)
            print(f"  Φ = {mult}*fc + rank_up: {phi_viol} violations ({pct:.1f}%)", flush=True)

        elapsed = time.time() - t0
        print(f"\n  Time: {elapsed:.1f}s", flush=True)

if __name__ == '__main__':
    main()
