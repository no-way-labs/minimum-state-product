#!/usr/bin/env python3
"""Extract explicit forced-successor loop data for the canonical Hamming-1 witness.

This probe reuses Probe C's cycle enumeration / witness construction and adds:

1. Full lex-first forced-successor traces with step labels
   `(mover, pre_value, post_value)`.
2. Per-n signature aggregation for the `2n+2` loops at `n = 5..8`.
3. Forward-closure graph extraction plus SCC analysis for `n = 9+`.
4. Exact search for cycles of specified length inside the forward closure
   (used to test whether a hidden `2n+2` loop survives at `n = 9`).

It deliberately does NOT reimplement cycle search, `det` construction, or the
Hamming-1 neighborhood machinery; those are imported from the existing probes.
"""

from collections import Counter, defaultdict, deque
import importlib.util
import json
import os
import time


_HERE = os.path.dirname(os.path.abspath(__file__))
_C_PATH = os.path.join(_HERE, "probe_sk_hamming1_chain_closure_2026-04-17.py")
_spec = importlib.util.spec_from_file_location("probe_c", _C_PATH)
probe_c = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(probe_c)

enumerate_cycles_multistart = probe_c.enumerate_cycles_multistart
build_N1_and_peel = probe_c.build_N1_and_peel
canonical_witness_from_peel = probe_c.canonical_witness_from_peel
forced_successors = probe_c.forced_successors
hamming = probe_c.hamming
m_n_sharp = probe_c.m_n_sharp


def find_off_value_coordinate(c_star, value_sets):
    offs = [i for i, vset in enumerate(value_sets) if c_star[i] not in vset]
    if len(offs) == 1:
        return offs[0]
    return None


def counter_items(counter):
    return [
        {"key": repr(key), "count": count}
        for key, count in counter.most_common()
    ]


def trace_chain_full(c_star, det, n, cycle_set, max_steps=5000):
    """Follow the same lex-first rule as Probe C, but keep full step data."""
    path = [c_star]
    visited = {c_star: 0}
    steps = []
    termination = None
    repeat_target = None
    loop_start = None

    for step_idx in range(max_steps):
        c = path[-1]
        succs = forced_successors(c, det, n, cycle_set)
        ng = [(p, nc) for (kind, p, nc) in succs if kind == "ng"]
        on_cycle = [(p, nc) for (kind, p, nc) in succs if kind == "cycle"]
        ng.sort(key=lambda item: item[1])
        on_cycle.sort(key=lambda item: item[1])
        step = {
            "step": step_idx,
            "from": list(c),
            "hamming": hamming(c, cycle_set),
            "ng_choices": [
                {
                    "mover": p,
                    "to": list(nc),
                    "pre": c[p],
                    "post": nc[p],
                }
                for p, nc in ng
            ],
            "cycle_choices": [
                {
                    "mover": p,
                    "to": list(nc),
                    "pre": c[p],
                    "post": nc[p],
                }
                for p, nc in on_cycle
            ],
        }

        if not ng and not on_cycle:
            termination = "dead_end"
            steps.append(step)
            break

        if not ng and on_cycle:
            termination = "reach_cycle"
            step["selected"] = {
                "kind": "cycle",
                "mover": on_cycle[0][0],
                "to": list(on_cycle[0][1]),
                "pre": c[on_cycle[0][0]],
                "post": on_cycle[0][1][on_cycle[0][0]],
            }
            steps.append(step)
            break

        p, nc = ng[0]
        step["selected"] = {
            "kind": "ng",
            "mover": p,
            "to": list(nc),
            "pre": c[p],
            "post": nc[p],
        }
        steps.append(step)

        if nc in visited:
            termination = "loop"
            repeat_target = nc
            loop_start = visited[nc]
            break

        visited[nc] = len(path)
        path.append(nc)

    if termination is None:
        termination = "max_steps"

    result = {
        "termination": termination,
        "path": [list(c) for c in path],
        "steps": steps,
        "repeat_target": list(repeat_target) if repeat_target is not None else None,
        "loop_start": loop_start,
        "loop_len": (len(path) - loop_start) if loop_start is not None else None,
        "path_hamming": [hamming(tuple(c), cycle_set) for c in path],
    }
    if loop_start is not None:
        result["loop_configs"] = [list(c) for c in path[loop_start:]]
        result["loop_steps"] = steps[loop_start:]
        result["loop_repeat_target"] = list(repeat_target)
    return result


def closure_graph(c_star, det, n, cycle_set):
    """Return the forward closure and adjacency restricted to VC_NG."""
    T = {c_star}
    frontier = deque([c_star])
    adj = defaultdict(set)
    cycle_touch = defaultdict(set)
    while frontier:
        c = frontier.popleft()
        for kind, p, nc in forced_successors(c, det, n, cycle_set):
            if kind == "ng":
                adj[c].add(nc)
                if nc not in T:
                    T.add(nc)
                    frontier.append(nc)
            else:
                cycle_touch[c].add((p, nc))
        if c not in adj:
            adj[c] = set()
    for c in list(T):
        adj[c] = sorted(adj[c])
        cycle_touch[c] = sorted(cycle_touch[c])
    return T, dict(adj), dict(cycle_touch)


def kosaraju_scc(adj):
    nodes = list(adj)
    radj = {u: [] for u in nodes}
    for u, vs in adj.items():
        for v in vs:
            radj.setdefault(v, []).append(u)
            if v not in adj:
                adj[v] = []
    order = []
    seen = set()

    def dfs1(u):
        seen.add(u)
        for v in adj[u]:
            if v not in seen:
                dfs1(v)
        order.append(u)

    for u in list(adj):
        if u not in seen:
            dfs1(u)

    comp_of = {}
    comps = []

    def dfs2(u, cid):
        comp_of[u] = cid
        comps[cid].append(u)
        for v in radj.get(u, []):
            if v not in comp_of:
                dfs2(v, cid)

    for u in reversed(order):
        if u in comp_of:
            continue
        comps.append([])
        dfs2(u, len(comps) - 1)

    comp_edges = {i: set() for i in range(len(comps))}
    for u, vs in adj.items():
        cu = comp_of[u]
        for v in vs:
            cv = comp_of[v]
            if cu != cv:
                comp_edges[cu].add(cv)

    bottom = sorted(cid for cid, outs in comp_edges.items() if not outs)
    return comp_of, comps, comp_edges, bottom


def reverse_bfs_dist(start, adj, allowed):
    radj = defaultdict(list)
    for u in allowed:
        for v in adj[u]:
            if v in allowed:
                radj[v].append(u)
    dist = {start: 0}
    q = deque([start])
    while q:
        u = q.popleft()
        for v in radj[u]:
            if v not in dist:
                dist[v] = dist[u] + 1
                q.append(v)
    return dist


def find_cycle_of_exact_length(adj, nodes, target_len):
    """Return one simple directed cycle of length target_len, else None."""
    allowed = set(nodes)
    for start in nodes:
        dist_to_start = reverse_bfs_dist(start, adj, allowed)
        if start not in dist_to_start:
            continue
        visited = {start}
        stack = [start]

        def dfs(u, depth):
            if depth == target_len:
                return stack + [start] if u == start else None
            rem = target_len - depth
            if dist_to_start.get(u, target_len + 1) > rem:
                return None
            for v in adj[u]:
                if v not in allowed:
                    continue
                if v == start:
                    if depth + 1 == target_len:
                        return stack + [start]
                    continue
                if v in visited:
                    continue
                if dist_to_start.get(v, target_len + 1) > (target_len - (depth + 1)):
                    continue
                visited.add(v)
                stack.append(v)
                got = dfs(v, depth + 1)
                if got is not None:
                    return got
                stack.pop()
                visited.remove(v)
            return None

        got = dfs(start, 0)
        if got is not None:
            return got
    return None


def shortest_cycle_through_node(adj, start):
    allowed = set(adj)
    q = deque([(start, 0)])
    seen = {start}
    while q:
        u, d = q.popleft()
        for v in adj[u]:
            if v == start and d + 1 > 0:
                return d + 1
            if v in allowed and v not in seen:
                seen.add(v)
                q.append((v, d + 1))
    return None


def normalize_step_signature(loop_steps, q0, n):
    return {
        "movers": [step["selected"]["mover"] for step in loop_steps],
        "relative_movers": [((step["selected"]["mover"] - q0) % n) if q0 is not None else None
                             for step in loop_steps],
        "triples": [
            (
                step["selected"]["mover"],
                step["selected"]["pre"],
                step["selected"]["post"],
            )
            for step in loop_steps
        ],
        "relative_triples": [
            (
                ((step["selected"]["mover"] - q0) % n) if q0 is not None else None,
                step["selected"]["pre"],
                step["selected"]["post"],
            )
            for step in loop_steps
        ],
    }


def analyze_cycle_record(n, ms, cycle, det):
    N1, adj_n1, peel_set, provenance, value_sets, _, cycle_set = build_N1_and_peel(
        ms, n, cycle, det
    )
    if not peel_set:
        return None
    c_star, q_list = canonical_witness_from_peel(peel_set, provenance, value_sets, ms, n, len(cycle))
    q0 = sorted(provenance[c_star])[0][0]
    q0_value_set_test = find_off_value_coordinate(c_star, value_sets)
    chain = trace_chain_full(c_star, det, n, cycle_set)
    T, adj, cycle_touch = closure_graph(c_star, det, n, cycle_set)
    comp_of, comps, comp_edges, bottom = kosaraju_scc(adj)
    cstar_comp = comp_of[c_star]
    analysis = {
        "n": n,
        "ms": list(ms),
        "L": len(cycle),
        "cycle": [list(c) for c in cycle],
        "c_star": list(c_star),
        "q_list": q_list,
        "q0": q0,
        "q0_value_set_test": q0_value_set_test,
        "provenance_entries": [list(item) for item in sorted(provenance[c_star])],
        "chain": chain,
        "T_size": len(T),
        "adj": {json.dumps(list(k)): [list(v) for v in vs] for k, vs in adj.items()},
        "cycle_touch": {
            json.dumps(list(k)): [{"mover": p, "to": list(nc)} for p, nc in vs]
            for k, vs in cycle_touch.items() if vs
        },
        "scc": {
            "count": len(comps),
            "sizes_desc": sorted((len(comp) for comp in comps), reverse=True),
            "bottom_ids": bottom,
            "bottom_sizes": [len(comps[cid]) for cid in bottom],
            "c_star_comp": cstar_comp,
            "c_star_comp_size": len(comps[cstar_comp]),
            "c_star_in_bottom": cstar_comp in bottom,
            "shortest_cycle_through_c_star": shortest_cycle_through_node(adj, c_star),
        },
    }
    if chain["termination"] == "loop":
        analysis["loop_signature"] = normalize_step_signature(chain["loop_steps"], q0, n)
    return analysis


def plans():
    return [
        (5, 15.0, 8, 13, [(2, 2, 2, 3, 3), (2, 2, 3, 3, 3), (2, 2, 2, 3, 4)]),
        (6, 20.0, 8, 15, [(2, 2, 2, 3, 3, 3), (2, 2, 3, 2, 3, 3), (2, 2, 2, 2, 3, 3)]),
        (7, 30.0, 6, 17, [(2, 2, 2, 3, 3, 3, 3), (2, 2, 3, 2, 3, 3, 3), (2, 2, 2, 2, 3, 3, 3)]),
        (8, 45.0, 5, 19, [(2, 2, 2, 3, 3, 3, 3, 3), (2, 2, 3, 2, 3, 3, 3, 3), (2, 2, 2, 2, 3, 3, 3, 3)]),
        (9, 60.0, 4, 22, [(2, 2, 2, 3, 3, 3, 3, 3, 3), (2, 2, 3, 2, 3, 3, 3, 3, 3), (2, 2, 2, 2, 3, 3, 3, 3, 3)]),
    ]


def main():
    out_dir = os.path.join(_HERE, "sk_2n2_loop_extract_out")
    os.makedirs(out_dir, exist_ok=True)

    all_records = []
    t0 = time.time()
    for n, tb, max_cycles, l_max, picked in plans():
        Mn = m_n_sharp(n)
        picked = [ms for ms in picked if __import__("math").prod(ms) < Mn]
        print(f"\n=== n={n} M_n={Mn} picked={picked}", flush=True)
        for ms in picked:
            cycles = enumerate_cycles_multistart(
                ms, n, L_min=2 * n + 2, L_max=l_max, time_budget=tb, max_cycles=max_cycles
            )
            print(f"  ms={ms} cycles_found={len(cycles)}", flush=True)
            for idx, (cycle, movers, det) in enumerate(cycles):
                rec = analyze_cycle_record(n, ms, cycle, det)
                if rec is None:
                    continue
                rec["cycle_index"] = idx
                if n >= 9:
                    target = 2 * n + 2
                    T_adj = {
                        tuple(json.loads(k)): [tuple(v) for v in vs]
                        for k, vs in rec["adj"].items()
                    }
                    comp_of, comps, _, bottom = kosaraju_scc({u: list(vs) for u, vs in T_adj.items()})
                    rec["scc"]["target_cycle_len"] = target
                    rec["scc"]["any_cycle_len_target"] = False
                    rec["scc"]["target_cycle_example"] = None
                    for cid in bottom:
                        nodes = comps[cid]
                        cyc = find_cycle_of_exact_length(T_adj, nodes, target)
                        if cyc is not None:
                            rec["scc"]["any_cycle_len_target"] = True
                            rec["scc"]["target_cycle_example"] = [list(c) for c in cyc]
                            break
                all_records.append(rec)
                chain = rec["chain"]
                print(
                    f"    cycle#{idx} c*={tuple(rec['c_star'])} q0={rec['q0']} "
                    f"term={chain['termination']} loop_len={chain['loop_len']} "
                    f"T={rec['T_size']} scc={rec['scc']['sizes_desc'][:5]}",
                    flush=True,
                )
        if time.time() - t0 > 55 * 60:
            print("[wall clock guard hit]", flush=True)
            break

    json_path = os.path.join(out_dir, "records.json")
    with open(json_path, "w") as f:
        json.dump(all_records, f, indent=2)

    summary = []
    by_n = defaultdict(list)
    for rec in all_records:
        by_n[rec["n"]].append(rec)
    for n in sorted(by_n):
        recs = by_n[n]
        terms = Counter(rec["chain"]["termination"] for rec in recs)
        loop_lens = Counter(rec["chain"]["loop_len"] for rec in recs if rec["chain"]["loop_len"] is not None)
        q0s = Counter(rec["q0"] for rec in recs)
        row = {
            "n": n,
            "count": len(recs),
            "termination": dict(terms),
            "loop_lens": dict(loop_lens),
            "q0s": dict(q0s),
            "unique_relative_movers": counter_items(Counter(
                tuple(rec["loop_signature"]["relative_movers"])
                for rec in recs if "loop_signature" in rec
            )),
            "unique_relative_triples": counter_items(Counter(
                tuple(rec["loop_signature"]["relative_triples"])
                for rec in recs if "loop_signature" in rec
            )),
            "scc_sizes_desc": counter_items(Counter(tuple(rec["scc"]["sizes_desc"]) for rec in recs)),
            "target_cycle_found": dict(Counter(
                rec["scc"].get("any_cycle_len_target") for rec in recs if n >= 9
            )),
        }
        summary.append(row)

    summary_path = os.path.join(out_dir, "summary.json")
    with open(summary_path, "w") as f:
        json.dump(summary, f, indent=2)

    print("\n" + "=" * 80)
    print("SK 2n+2 loop extraction summary")
    print("=" * 80)
    for row in summary:
        print(
            f"n={row['n']} count={row['count']} term={row['termination']} "
            f"loop_lens={row['loop_lens']} q0s={row['q0s']}",
            flush=True,
        )
        if row["unique_relative_movers"]:
            print(f"  unique_relative_movers={len(row['unique_relative_movers'])}", flush=True)
        if row["unique_relative_triples"]:
            print(f"  unique_relative_triples={len(row['unique_relative_triples'])}", flush=True)
        if row["target_cycle_found"]:
            print(f"  target_cycle_found={dict(row['target_cycle_found'])}", flush=True)
        print(f"  scc_sizes_desc_variants={len(row['scc_sizes_desc'])}", flush=True)
    print(f"\nrecords: {json_path}")
    print(f"summary: {summary_path}")


if __name__ == "__main__":
    main()
