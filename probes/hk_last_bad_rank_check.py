#!/usr/bin/env python3
from __future__ import annotations

import os
import sys
from collections import defaultdict, Counter, deque

ROOT = os.path.dirname(os.path.dirname(__file__))
GPT_SCRIPTS = os.path.join(ROOT, "gpt", "scripts")
sys.path.insert(0, GPT_SCRIPTS)

from p2_good_cycle_search import enumerate_good_cycles  # type: ignore
from p2_cycle_screen import forced_rule_map  # type: ignore
from p2_completion_search import screening_data  # type: ignore


def local_five(t: int, n: int) -> set[int]:
    return {(t - 2) % n, (t - 1) % n, t, (t + 1) % n, (t + 2) % n}


def pivots(ms: tuple[int, ...]) -> list[int]:
    n = len(ms)
    return [i for i in range(n) if ms[(i - 1) % n] == 2 and ms[(i + 1) % n] == 2]


def hk_last_instances(movers: tuple[int, ...], n: int, pivs: list[int]) -> list[tuple[int, int]]:
    hits = []
    for t in pivs:
        outside = [idx for idx, mover in enumerate(movers) if mover not in local_five(t, n)]
        if outside and outside[-1] + 1 == len(movers):
            hits.append((t, outside[-1]))
    return hits


def tarjan_scc(adjacency: list[list[int]]) -> list[list[int]]:
    index = 0
    stack: list[int] = []
    on_stack: set[int] = set()
    indices = [-1] * len(adjacency)
    lowlinks = [0] * len(adjacency)
    components: list[list[int]] = []

    def strongconnect(node: int) -> None:
        nonlocal index
        indices[node] = index
        lowlinks[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)
        for dst in adjacency[node]:
            if indices[dst] == -1:
                strongconnect(dst)
                lowlinks[node] = min(lowlinks[node], lowlinks[dst])
            elif dst in on_stack:
                lowlinks[node] = min(lowlinks[node], indices[dst])
        if lowlinks[node] != indices[node]:
            return
        comp = []
        while True:
            top = stack.pop()
            on_stack.remove(top)
            comp.append(top)
            if top == node:
                break
        components.append(comp)

    for node in range(len(adjacency)):
        if indices[node] == -1:
            strongconnect(node)
    return components


def is_forward_sweep(movers: tuple[int, ...], n: int) -> bool:
    return all(movers[k] == (k % n) for k in range(len(movers)))


def is_reverse_sweep(movers: tuple[int, ...], n: int) -> bool:
    return all(movers[k] == ((-k) % n) for k in range(len(movers)))


def analyze(cycle, movers, ms):
    cycle_set = frozenset(cycle)
    fm = forced_rule_map(cycle, movers)
    data = screening_data(ms)
    outgoing_bad = [[] for _ in data.configs]
    reverse_bad = [[] for _ in data.configs]
    bad_indices = [idx for idx, cfg in enumerate(data.configs) if cfg not in cycle_set]
    for idx, cfg in enumerate(data.configs):
        if cfg in cycle_set:
            continue
        for proc, key in enumerate(data.config_keys[idx]):
            out = fm.get(key)
            if out is None or out == cfg[proc]:
                continue
            nxt = list(cfg)
            nxt[proc] = out
            dst = data.index[tuple(nxt)]
            if data.configs[dst] in cycle_set:
                continue
            outgoing_bad[idx].append(dst)
            reverse_bad[dst].append(idx)

    sccs = [comp for comp in tarjan_scc(outgoing_bad) if len(comp) > 1]
    inf_nodes = set().union(*map(set, sccs)) if sccs else set()
    changed = True
    while changed:
        changed = False
        for idx, dsts in enumerate(outgoing_bad):
            if idx in inf_nodes:
                continue
            if any(dst in inf_nodes for dst in dsts):
                inf_nodes.add(idx)
                changed = True

    # finite rank on residual DAG (distance to dead end), only for nodes not in inf_nodes
    outdeg_res = {
        idx: sum(1 for dst in outgoing_bad[idx] if dst not in inf_nodes)
        for idx in bad_indices if idx not in inf_nodes
    }
    q = deque([idx for idx, d in outdeg_res.items() if d == 0])
    rank = {idx: 0 for idx in q}
    while q:
        v = q.popleft()
        for src in reverse_bad[v]:
            if src in inf_nodes:
                continue
            cand = rank[v] + 1
            if cand > rank.get(src, -1):
                rank[src] = cand
            outdeg_res[src] -= 1
            if outdeg_res[src] == 0:
                q.append(src)
    return inf_nodes, rank, sccs, data, bad_indices


def main() -> None:
    n = 7
    ms = (2,) * n
    pivs = pivots(ms)
    seen = 0
    for cycle, movers in enumerate_good_cycles(ms, max_cycles=80, time_limit=8.0):
        hits = hk_last_instances(movers, n, pivs)
        if not hits:
            continue
        if is_forward_sweep(movers, n) or is_reverse_sweep(movers, n):
            continue
        seen += 1
        inf_nodes, rank, sccs, data, bad_indices = analyze(cycle, movers, ms)
        bad_total = len(bad_indices)
        finite_nodes = len([idx for idx in bad_indices if idx not in inf_nodes])
        print(f"\n=== non-sweep witness {seen} ===")
        print(f"movers={movers}")
        print(f"hits={hits}")
        print(f"bad_total={bad_total} infinite_rank_nodes={len(inf_nodes)} finite_rank_nodes={finite_nodes}")
        print(f"scc_sizes={sorted(len(comp) for comp in sccs)}")
        rc = Counter(rank.values())
        print(f"finite rank distribution={dict(sorted(rc.items()))}")
        if seen >= 5:
            break


if __name__ == "__main__":
    main()
