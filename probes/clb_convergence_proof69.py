#!/usr/bin/env python3
"""
CONVERGENCE PROOF 69: Stratified structure within (int21,intj20) components
===========================================================================
Within each component, fc varies in [-(n-3), +2]. Key questions:
1. Is the Δfc≥0 subgraph a DAG? What rank?
2. Is the Δfc>0 subgraph a DAG? What rank?
3. Can we decompose each edge into: anomalous step (which entry?) + path
4. Which anomalous entries appear in Δfc>0 edges?
5. For cycles to exist: need Σ Δfc = 0. What's the structure?

Also: test (fc, Ψ) lexicographic potential within components,
where Ψ is some function that decreases on Δfc=0 edges.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter, deque

def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))

def build_excursion_graph_detailed(n_val):
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
            L = c[(i-1) % n_val]; S = c[i]; R = c[(i+1) % n_val]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    dfc = delta_fc(L, S, R, out)
                    if dfc <= 0:
                        dfc_le0_adj[c].append(succ)
                    if out != L and out != R:
                        anom_edges.append((c, succ, i, dfc, L, S, R, out))
    anom_sources = set(c for c, _, _, _, _, _, _, _ in anom_edges)
    anom_target_map = defaultdict(list)
    anom_info = {}
    for c, succ, i, dfc, L, S, R, out in anom_edges:
        anom_target_map[succ].append(c)
        anom_info[(c, succ)] = (i, L, S, R, out, dfc)
    exc_edges = []
    for b in set(s for _, s, _, _, _, _, _, _ in anom_edges):
        visited = {b}
        queue = [b]
        head = 0
        while head < len(queue):
            node = queue[head]; head += 1
            if node in anom_sources:
                for src in anom_target_map.get(b, []):
                    exc_edges.append((src, node, b))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append(nxt)
    return exc_edges, ms, fs, anom_info

def int_21(c, n):
    return sum(1 for j in range(2, n-2) if c[j] == 2 and c[(j+1) % n] == 1)

def int_j_20(c, n):
    return sum(j for j in range(2, n-2) if c[j] == 2 and c[(j+1) % n] == 0)

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j+1) % n])

def dag_info(edges, nodes):
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
    if not is_dag:
        return False, -1
    rk = {}
    for c in reversed(topo):
        rk[c] = max((rk[s] + 1 for s in adj[c]), default=0)
    return True, max(rk.values()) if rk else 0

def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges_d, ms, fs, anom_info = build_excursion_graph_detailed(n_val)
        n = n_val

        # Build jdz with intermediate info
        jdz = []
        for u, v, b in exc_edges_d:
            if int_21(v, n) - int_21(u, n) != 0:
                continue
            if int_j_20(v, n) - int_j_20(u, n) != 0:
                continue
            jdz.append((u, v, b))
        jdz_unique = list(set((u, v) for u, v, b in jdz))

        if not jdz_unique:
            print(f"n={n}: no jdz edges")
            continue

        print(f"\n{'=' * 70}", flush=True)
        print(f"n={n}: {len(jdz_unique)} jdz edges ({time.time() - t0:.1f}s)", flush=True)
        print(f"{'=' * 70}", flush=True)

        # Group by (int21, intj20)
        comp_edges = defaultdict(list)
        comp_nodes = defaultdict(set)
        for u, v in jdz_unique:
            key = (int_21(u, n), int_j_20(u, n))
            comp_edges[key].append((u, v))
            comp_nodes[key].add(u)
            comp_nodes[key].add(v)

        # For the dominant component (int21=1, intj20=0), do detailed analysis
        dom_key = max(comp_edges.keys(), key=lambda k: len(comp_edges[k]))
        dom_edges = comp_edges[dom_key]
        dom_nodes = comp_nodes[dom_key]

        print(f"\n  Dominant component: {dom_key}, {len(dom_edges)} edges, {len(dom_nodes)} nodes", flush=True)

        # === 1. Δfc≥0 subgraph ===
        up_edges = [(u, v) for u, v in dom_edges if fc(v, n) >= fc(u, n)]
        up_nodes = set()
        for u, v in up_edges:
            up_nodes.add(u)
            up_nodes.add(v)
        if up_edges:
            is_dag, max_r = dag_info(up_edges, up_nodes)
            print(f"  Δfc≥0 subgraph: {len(up_edges)} edges, {len(up_nodes)} nodes, DAG={is_dag}, rank={max_r}", flush=True)

        # === 2. Δfc>0 subgraph ===
        up_strict = [(u, v) for u, v in dom_edges if fc(v, n) > fc(u, n)]
        up_strict_nodes = set()
        for u, v in up_strict:
            up_strict_nodes.add(u)
            up_strict_nodes.add(v)
        if up_strict:
            is_dag, max_r = dag_info(up_strict, up_strict_nodes)
            print(f"  Δfc>0 subgraph: {len(up_strict)} edges, {len(up_strict_nodes)} nodes, DAG={is_dag}, rank={max_r}", flush=True)

        # === 3. Δfc=0 subgraph ===
        level_edges = [(u, v) for u, v in dom_edges if fc(v, n) == fc(u, n)]
        level_nodes = set()
        for u, v in level_edges:
            level_nodes.add(u)
            level_nodes.add(v)
        if level_edges:
            is_dag, max_r = dag_info(level_edges, level_nodes)
            print(f"  Δfc=0 subgraph: {len(level_edges)} edges, {len(level_nodes)} nodes, DAG={is_dag}, rank={max_r}", flush=True)

        # === 4. Per-fc-level subgraphs within this component ===
        by_fc = defaultdict(list)
        for u, v in dom_edges:
            by_fc[fc(u, n)].append((u, v))

        print(f"\n  Per-fc-level within dominant component:", flush=True)
        for fc_val in sorted(by_fc.keys()):
            edges = by_fc[fc_val]
            nodes = set()
            for u, v in edges:
                nodes.add(u)
                nodes.add(v)
            is_dag, max_r = dag_info(edges, nodes)
            # Δfc distribution within this fc level
            dfcs = Counter(fc(v, n) - fc(u, n) for u, v in edges)
            print(f"    fc={fc_val}: {len(edges)} edges, {len(nodes)} nodes, DAG={is_dag}, rank={max_r}, Δfc={dict(sorted(dfcs.items()))}", flush=True)

        # === 5. Which anomalous entries appear in Δfc>0 edges? ===
        print(f"\n  Anomalous entries in Δfc>0 jdz edges:", flush=True)
        entry_count = Counter()
        for u, v, b in jdz:
            key = (int_21(u, n), int_j_20(u, n))
            if key != dom_key:
                continue
            dfc = fc(v, n) - fc(u, n)
            if dfc > 0:
                info = anom_info.get((u, b))
                if info:
                    pos, L, S, R, out, step_dfc = info
                    ptype = 'bot' if pos == 0 else 'low' if pos == 1 else 'high' if pos == n - 2 else 'top' if pos == n - 1 else 'mid'
                    entry_count[(ptype, L, S, R, out)] += 1

        for (ptype, L, S, R, out), cnt in entry_count.most_common(20):
            print(f"    {ptype}({L},{S},{R})→{out}: {cnt}", flush=True)

        # === 6. Test Ψ = Σ_j j · [c[j]=2] within Δfc=0 edges of component ===
        print(f"\n  Ψ tests on Δfc=0 edges within dominant component:", flush=True)
        lev = [(u, v) for u, v in dom_edges if fc(v, n) == fc(u, n)]
        if lev:
            tests = {
                'Σj·[c[j]=2]': lambda c: sum(j for j in range(n) if c[j] == 2),
                'Σj²·[c[j]=2]': lambda c: sum(j * j for j in range(n) if c[j] == 2),
                'Σc[j]': lambda c: sum(c),
                'Σj·c[j]': lambda c: sum(j * c[j] for j in range(n)),
                '#(c[j]=2)': lambda c: sum(1 for x in c if x == 2),
                '#(c[j]=0)': lambda c: sum(1 for x in c if x == 0),
                'max_pos_2': lambda c: max((j for j in range(n) if c[j] == 2), default=-1),
                'min_pos_0': lambda c: min((j for j in range(n) if c[j] == 0), default=n),
            }
            for tname, tfunc in tests.items():
                viol_dec = sum(1 for u, v in lev if tfunc(v) >= tfunc(u))
                viol_inc = sum(1 for u, v in lev if tfunc(v) <= tfunc(u))
                best = min(viol_dec, viol_inc)
                bdir = 'dec' if viol_dec <= viol_inc else 'inc'
                pct = 100 * best / len(lev) if lev else 0
                marker = " ***" if best == 0 else ""
                print(f"    {tname:20s}: {bdir} {best}/{len(lev)} ({pct:.1f}%){marker}", flush=True)

        # === 7. ALL components: Δfc≥0 subgraph DAG check ===
        print(f"\n  Δfc≥0 subgraph DAG check (all components):", flush=True)
        all_up_dag = True
        max_up_rank = 0
        for key in sorted(comp_edges.keys(), key=lambda k: -len(comp_edges[k])):
            edges = comp_edges[key]
            up_e = [(u, v) for u, v in edges if fc(v, n) >= fc(u, n)]
            if not up_e:
                continue
            up_n = set()
            for u, v in up_e:
                up_n.add(u)
                up_n.add(v)
            is_dag, max_r = dag_info(up_e, up_n)
            if not is_dag:
                all_up_dag = False
                print(f"    {key}: NOT DAG!", flush=True)
            else:
                max_up_rank = max(max_up_rank, max_r)
        print(f"  All Δfc≥0 subgraphs DAG: {all_up_dag}, max rank: {max_up_rank}", flush=True)

        # === 8. Δfc=0 subgraph DAG check (all components) ===
        print(f"\n  Δfc=0 subgraph DAG check (all components):", flush=True)
        all_lev_dag = True
        max_lev_rank = 0
        for key in sorted(comp_edges.keys(), key=lambda k: -len(comp_edges[k])):
            edges = comp_edges[key]
            lev_e = [(u, v) for u, v in edges if fc(v, n) == fc(u, n)]
            if not lev_e:
                continue
            lev_n = set()
            for u, v in lev_e:
                lev_n.add(u)
                lev_n.add(v)
            is_dag, max_r = dag_info(lev_e, lev_n)
            if not is_dag:
                all_lev_dag = False
                print(f"    {key}: NOT DAG!", flush=True)
            else:
                max_lev_rank = max(max_lev_rank, max_r)
        print(f"  All Δfc=0 subgraphs DAG: {all_lev_dag}, max rank: {max_lev_rank}", flush=True)

        elapsed = time.time() - t0
        print(f"\n  Total time: {elapsed:.1f}s", flush=True)

if __name__ == '__main__':
    main()
