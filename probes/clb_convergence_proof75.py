#!/usr/bin/env python3
"""
CONVERGENCE PROOF 75: Sub-component decomposition of jdz
=========================================================
KEY HYPOTHESIS: int_j(2,1) is preserved on jdz edges, giving finer decomposition.
Within each (int_21, int_j_20, int_j_21) sub-component:
- Only boundary entries (1,2,4,5) drive excursion edges (entry 3 excluded)
- The (2,1) pair at position j is frozen
- Sub-component rank depends on j

Verify:
1. Is int_j(2,1) preserved on jdz edges?
2. Decompose by (int_21, int_j_20, int_j_21) - per-component ranks?
3. Which anomalous entries drive edges within each sub-component?
4. Do sub-components have simpler potential functions?
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

def classify_anom(pos, L, S, R, out, n):
    if pos == 0:
        return f"bot({L},{S},{R})→{out}"
    elif pos == 1:
        return f"low({L},{S},{R})→{out}"
    elif pos == n - 2:
        return f"high({L},{S},{R})→{out}"
    elif pos == n - 1:
        return f"top({L},{S},{R})→{out}"
    else:
        return f"mid({L},{S},{R})→{out}"

def build_exc_with_info(n_val):
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
    anom_step_info = {}
    for c, succ, i, dfc in anom_edges:
        anom_target_map[succ].append(c)
        anom_step_info[(c, succ)] = (i, c[(i-1)%n_val], c[i], c[(i+1)%n_val], succ[i])
    exc_edges = []
    for b in set(s for _, s, _, _ in anom_edges):
        visited = {b}
        queue = [b]
        head = 0
        while head < len(queue):
            node = queue[head]
            head += 1
            if node in anom_sources:
                for src in anom_target_map.get(b, []):
                    info = anom_step_info.get((src, b))
                    exc_edges.append((src, node, info))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append(nxt)
    return exc_edges, ms, fs

def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def int_j_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def int_j_21(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def int_20(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges_full, ms, fs = build_exc_with_info(n_val)
        n = n_val

        # Build jdz with entry info
        jdz_with_info = []
        jdz_set = set()
        for u, v, info in exc_edges_full:
            if int_21(v, n) - int_21(u, n) != 0:
                continue
            if int_j_20(v, n) - int_j_20(u, n) != 0:
                continue
            if (u, v) not in jdz_set:
                jdz_set.add((u, v))
                jdz_with_info.append((u, v, info))

        jdz = list(jdz_set)
        if not jdz:
            print(f"n={n}: no jdz edges")
            continue

        print(f"\n{'=' * 70}", flush=True)
        print(f"n={n}: {len(jdz)} jdz edges ({time.time()-t0:.1f}s)", flush=True)
        print(f"{'=' * 70}", flush=True)

        # === 1. Check: is int_j_21 preserved on jdz edges? ===
        violations_j21 = 0
        violations_20 = 0
        dj21_dist = Counter()
        for u, v in jdz:
            dj21 = int_j_21(v, n) - int_j_21(u, n)
            d20 = int_20(v, n) - int_20(u, n)
            dj21_dist[dj21] += 1
            if dj21 != 0:
                violations_j21 += 1
            if d20 != 0:
                violations_20 += 1

        print(f"\n  int_j_21 preserved? {violations_j21 == 0} ({violations_j21} violations)", flush=True)
        print(f"  int_20 preserved? {violations_20 == 0} ({violations_20} violations)", flush=True)
        if violations_j21 > 0:
            print(f"  Δint_j_21 distribution: {dict(sorted(dj21_dist.items()))}", flush=True)

        # === 2. Decompose by (int_21, int_j_20, int_j_21) ===
        comp_edges = defaultdict(list)
        comp_nodes = defaultdict(set)
        comp_edge_info = defaultdict(list)
        for u, v, info in jdz_with_info:
            key = (int_21(u, n), int_j_20(u, n), int_j_21(u, n))
            comp_edges[key].append((u, v))
            comp_nodes[key].add(u)
            comp_nodes[key].add(v)
            comp_edge_info[key].append((u, v, info))

        print(f"\n  Sub-components by (int_21, int_j_20, int_j_21):", flush=True)
        for key in sorted(comp_edges.keys(), key=lambda k: -len(comp_edges[k])):
            edges = comp_edges[key]
            nodes = comp_nodes[key]

            # Compute DAG rank
            adj = defaultdict(list)
            for u, v in edges:
                adj[u].append(v)
            in_deg = defaultdict(int)
            for u, v in edges:
                in_deg[v] += 1
            q = deque([u for u in nodes if in_deg[u] == 0])
            topo = []
            while q:
                node = q.popleft()
                topo.append(node)
                for nxt in adj[node]:
                    in_deg[nxt] -= 1
                    if in_deg[nxt] == 0:
                        q.append(nxt)
            is_dag = len(topo) == len(nodes)

            if is_dag:
                rk = {}
                for c in reversed(topo):
                    rk[c] = max((rk[s] + 1 for s in adj[c]), default=0)
                max_r = max(rk.values()) if rk else 0
            else:
                max_r = -1

            # fc range
            fc_vals = [fc(c, n) for c in nodes]
            fc_min, fc_max = min(fc_vals), max(fc_vals)

            # Dead ends (no outgoing edges)
            dead_ends = sum(1 for c in nodes if not adj.get(c))

            i21, ij20, ij21 = key
            # Position of (2,1) pair for int_21=1
            pos_str = f" pos21={ij21}" if i21 == 1 else ""

            print(f"    {key}{pos_str}: {len(nodes)} nodes, {len(edges)} edges, "
                  f"DAG={is_dag}, rank={max_r}, fc=[{fc_min},{fc_max}], "
                  f"dead_ends={dead_ends}", flush=True)

        # === 3. Which anomalous entries drive edges in dominant sub-components? ===
        print(f"\n  Entry types per sub-component:", flush=True)
        for key in sorted(comp_edges.keys(), key=lambda k: -len(comp_edges[k]))[:5]:
            edge_infos = comp_edge_info[key]
            entry_types = Counter()
            for u, v, info in edge_infos:
                if info:
                    pos, L, S, R, out = info
                    etype = classify_anom(pos, L, S, R, out, n)
                    entry_types[etype] += 1
                else:
                    entry_types["(unknown)"] += 1

            print(f"    {key}:", flush=True)
            for etype, cnt in entry_types.most_common(10):
                print(f"      {etype}: {cnt}", flush=True)

        # === 4. Within largest sub-component: test potential functions ===
        dom_key = max(comp_edges.keys(), key=lambda k: len(comp_edges[k]))
        dom_edges = comp_edges[dom_key]
        dom_nodes = comp_nodes[dom_key]

        if len(dom_edges) > 5:
            adj = defaultdict(list)
            for u, v in dom_edges:
                adj[u].append(v)
            in_deg = defaultdict(int)
            for u, v in dom_edges:
                in_deg[v] += 1
            q = deque([u for u in dom_nodes if in_deg[u] == 0])
            topo = []
            while q:
                node = q.popleft()
                topo.append(node)
                for nxt in adj[node]:
                    in_deg[nxt] -= 1
                    if in_deg[nxt] == 0:
                        q.append(nxt)

            if len(topo) == len(dom_nodes):
                rk = {}
                for c in reversed(topo):
                    rk[c] = max((rk[s] + 1 for s in adj[c]), default=0)

                # Test simple potential: -fc (should work if fc always increases)
                tests = {
                    '-fc': lambda c: -fc(c, n),
                    'fc': lambda c: fc(c, n),
                    '#int_2': lambda c: sum(1 for j in range(2, n-2) if c[j] == 2),
                    '#int_0': lambda c: sum(1 for j in range(2, n-2) if c[j] == 0),
                    'sum_int': lambda c: sum(c[j] for j in range(2, n-2)),
                    'j_sum_int': lambda c: sum(j * c[j] for j in range(2, n-2)),
                    'max_pos_2': lambda c: max((j for j in range(2, n-2) if c[j] == 2), default=-1),
                    'min_pos_0': lambda c: min((j for j in range(2, n-2) if c[j] == 0), default=n),
                    '-P0-P1': lambda c: -c[0] - c[1],
                    'P0+Pn1': lambda c: c[0] + c[n-1],
                    'bdry_sum': lambda c: c[0] + c[1] + c[n-2] + c[n-1],
                    '-bdry_sum': lambda c: -(c[0] + c[1] + c[n-2] + c[n-1]),
                }

                print(f"\n  Potential tests in dominant sub-component {dom_key} "
                      f"({len(dom_edges)} edges):", flush=True)
                for tname, tfunc in tests.items():
                    strictly_dec = sum(1 for u, v in dom_edges if tfunc(v) < tfunc(u))
                    non_inc = sum(1 for u, v in dom_edges if tfunc(v) <= tfunc(u))
                    viol = len(dom_edges) - non_inc
                    viol_strict = len(dom_edges) - strictly_dec
                    pct = 100 * viol / len(dom_edges)
                    pct_strict = 100 * viol_strict / len(dom_edges)
                    marker = " *** MONOTONE" if viol == 0 else " ** strict" if viol_strict == 0 else ""
                    print(f"    {tname:20s}: non-inc violations={viol} ({pct:.1f}%), "
                          f"strict={viol_strict} ({pct_strict:.1f}%){marker}", flush=True)

                # Correlation of full rank with each test
                print(f"\n  Full rank correlation:", flush=True)
                ys = [rk[c] for c in dom_nodes]
                y_mean = sum(ys) / len(ys) if ys else 0
                ss_tot = sum((y - y_mean)**2 for y in ys) or 1
                for tname, tfunc in tests.items():
                    xs = [tfunc(c) for c in dom_nodes]
                    x_mean = sum(xs) / len(xs)
                    ss_xx = sum((x - x_mean)**2 for x in xs) or 1
                    ss_xy = sum((x - x_mean)*(y - y_mean) for x, y in zip(xs, ys))
                    b1 = ss_xy / ss_xx
                    b0 = y_mean - b1 * x_mean
                    ss_res = sum((y - (b0 + b1*x))**2 for x, y in zip(xs, ys))
                    r2 = 1 - ss_res / ss_tot
                    print(f"    {tname:20s}: R² = {r2:.4f}, slope={b1:.3f}", flush=True)

        elapsed = time.time() - t0
        print(f"\n  Time: {elapsed:.1f}s", flush=True)

if __name__ == '__main__':
    main()
