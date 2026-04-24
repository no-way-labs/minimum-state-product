#!/usr/bin/env python3
"""Probe the unique-dead-end / peel-cascade structure in T(c*).

Uses the existing extraction machinery and extracted records. Goals:

1. Identify zero-outdegree nodes in T(c*) and relate them to the lex-first path.
2. Test whether removing the unique dead-end leaves a forced-closed set.
3. Compute the full peel cascade (round-by-round removed nodes).
4. Compare against small-n extracted records where T(c*) is already closed.

This probe deliberately reuses the existing extraction infrastructure.
"""

from collections import defaultdict, deque
import importlib.util
import json
import os


_HERE = os.path.dirname(os.path.abspath(__file__))
_EXTRACT_PATH = os.path.join(_HERE, "probe_sk_2n2_loop_extract_2026-04-17.py")
_spec = importlib.util.spec_from_file_location("probe_extract", _EXTRACT_PATH)
probe_extract = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(probe_extract)


def decode_adj(rec):
    return {tuple(json.loads(k)): [tuple(v) for v in vs] for k, vs in rec["adj"].items()}


def decode_cycle_touch(rec):
    return {
        tuple(json.loads(k)): [(d["mover"], tuple(d["to"])) for d in vs]
        for k, vs in rec.get("cycle_touch", {}).items()
    }


def peel_rounds(adj):
    cur = set(adj)
    rounds = []
    while True:
        removed = sorted(u for u in cur if not any(v in cur for v in adj[u]))
        rounds.append(removed)
        if not removed:
            break
        cur -= set(removed)
    return rounds, cur


def shortest_distances(adj, start):
    dist = {start: 0}
    q = deque([start])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v not in dist:
                dist[v] = dist[u] + 1
                q.append(v)
    return dist


def mover_between(a, b):
    diffs = [i for i, (x, y) in enumerate(zip(a, b)) if x != y]
    if len(diffs) != 1:
        return None
    return diffs[0]


def analyze_record(rec):
    adj = decode_adj(rec)
    cycle_touch = decode_cycle_touch(rec)
    cstar = tuple(rec["c_star"])
    zero_nodes = sorted([c for c, vs in adj.items() if len(vs) == 0])
    lex_path = [tuple(c) for c in rec["chain"]["path"]]
    lex_terminal = lex_path[-1]
    dist = shortest_distances(adj, cstar)
    rounds, core = peel_rounds(adj)

    return {
        "n": rec["n"],
        "ms": rec["ms"],
        "cycle_index": rec["cycle_index"],
        "L": rec["L"],
        "c_star": rec["c_star"],
        "q0": rec["q0"],
        "good_word": [
            mover_between(tuple(rec["cycle"][i]), tuple(rec["cycle"][(i + 1) % len(rec["cycle"])]))
            for i in range(len(rec["cycle"]))
        ],
        "lex_word": [step["selected"]["mover"] for step in rec["chain"]["steps"] if step.get("selected")],
        "lex_terminal": list(lex_terminal),
        "zero_outdegree_count": len(zero_nodes),
        "zero_nodes": [list(z) for z in zero_nodes],
        "zero_cycle_touch": {
            json.dumps(list(z)): [
                {"mover": p, "to": list(nc)} for p, nc in cycle_touch.get(z, [])
            ]
            for z in zero_nodes
        },
        "zero_dists_from_cstar": {json.dumps(list(z)): dist.get(z) for z in zero_nodes},
        "lex_terminal_is_zero": lex_terminal in zero_nodes,
        "one_step_peel_closed": False if not zero_nodes else all(
            any(v != zero_nodes[0] for v in adj[u]) for u in adj if u != zero_nodes[0]
        ),
        "peel_round_sizes": [len(r) for r in rounds],
        "peel_round_nodes": [[list(x) for x in r] for r in rounds if r],
        "core_size": len(core),
    }


def main():
    out_dir = os.path.join(_HERE, "sk_deadend_peel_out")
    os.makedirs(out_dir, exist_ok=True)

    # Part A/B on extracted n=5..9 records
    extract_json = os.path.join(_HERE, "sk_2n2_loop_extract_out", "records.json")
    with open(extract_json) as f:
        records = json.load(f)

    analyzed = []
    for rec in records:
        analyzed.append(analyze_record(rec))

    # Add a fresh canonical n=10 sample set
    n10_records = []
    n = 10
    ms = (2, 2, 2, 2, 3, 3, 3, 3, 3, 3)
    cycles = probe_extract.enumerate_cycles_multistart(
        ms, n, L_min=2 * n + 2, L_max=24, time_budget=600.0, max_cycles=2
    )
    for idx, (cycle, movers, det) in enumerate(cycles):
        rec = probe_extract.analyze_cycle_record(n, ms, cycle, det)
        if rec is None:
            continue
        rec["cycle_index"] = idx
        analyzed.append(analyze_record(rec))
        n10_records.append(analyze_record(rec))

    out_json = os.path.join(out_dir, "records.json")
    with open(out_json, "w") as f:
        json.dump(analyzed, f, indent=2)

    print("=" * 80)
    print("Dead-end / peel probe summary")
    print("=" * 80)
    for n in sorted({r["n"] for r in analyzed}):
        recs = [r for r in analyzed if r["n"] == n]
        print(f"\nn={n} count={len(recs)}")
        zero_counts = defaultdict(int)
        one_step = defaultdict(int)
        round_sigs = defaultdict(int)
        for r in recs:
            zero_counts[r["zero_outdegree_count"]] += 1
            one_step[r["one_step_peel_closed"]] += 1
            round_sigs[tuple(r["peel_round_sizes"])] += 1
        print(f"  zero_outdegree_count={dict(zero_counts)}")
        print(f"  one_step_peel_closed={dict(one_step)}")
        print(f"  peel_round_sizes={dict(round_sigs)}")
        rep = recs[0]
        print(f"  rep c*={tuple(rep['c_star'])} q0={rep['q0']}")
        print(f"  rep lex_terminal={tuple(rep['lex_terminal'])}")
        print(f"  rep zero_nodes={[tuple(z) for z in rep['zero_nodes']]}")
        print(f"  rep zero_dists={rep['zero_dists_from_cstar']}")
        if rep["peel_round_nodes"]:
            print("  rep peel rounds:")
            for i, nodes in enumerate(rep["peel_round_nodes"], start=1):
                print(f"    round {i}: {[tuple(x) for x in nodes]}")

    print(f"\njson: {out_json}")


if __name__ == "__main__":
    main()
