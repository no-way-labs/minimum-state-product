#!/usr/bin/env python3
from __future__ import annotations

import os
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(__file__))
GPT_SCRIPTS = os.path.join(ROOT, "gpt", "scripts")
sys.path.insert(0, GPT_SCRIPTS)

from p2_good_cycle_search import enumerate_good_cycles  # type: ignore
from p2_cycle_screen import forced_rule_map  # type: ignore
from p2_completion_search import screening_data  # type: ignore


def local_five(t: int, n: int) -> set[int]:
    return {(t - 2) % n, (t - 1) % n, t, (t + 1) % n, (t + 2) % n}


def hk_last_instances(movers: tuple[int, ...], n: int, pivots: list[int]) -> list[tuple[int, int]]:
    hits = []
    for t in pivots:
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


def extract_bad_cycle(cycle, movers, state_counts):
    cycle_set = frozenset(cycle)
    fm = forced_rule_map(cycle, movers)
    data = screening_data(state_counts)
    edges: dict[int, list[tuple[int, int]]] = defaultdict(list)
    adjacency = [[] for _ in data.configs]
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
            edges[idx].append((proc, dst))
            adjacency[idx].append(dst)
    scc = [comp for comp in tarjan_scc(adjacency) if len(comp) > 1][0]
    scc_set = set(scc)
    start = next(iter(scc_set))
    seen = {}
    path: list[tuple[int, int]] = []
    node = start
    while True:
        if node in seen:
            cyc = path[seen[node]:]
            break
        seen[node] = len(path)
        proc, dst = [(p, d) for p, d in edges[node] if d in scc_set][0]
        path.append((node, proc))
        node = dst
    bad_cfgs = tuple(data.configs[node] for node, _ in cyc)
    bad_movers = tuple(proc for _, proc in cyc)
    return bad_cfgs, bad_movers


def hentry_exists_for_step(good_cycle, bad_cfgs, bad_movers, k):
    n = len(good_cycle[0])
    q = bad_movers[k]
    bad = bad_cfgs[k]
    bad_next = bad_cfgs[(k + 1) % len(bad_cfgs)]
    matches = []
    for j, good in enumerate(good_cycle):
        if bad[q] != good[q]:
            continue
        if bad[(q - 1) % n] != good[(q - 1) % n]:
            continue
        if bad[(q + 1) % n] != good[(q + 1) % n]:
            continue
        if bad_next[q] != good_cycle[(j + 1) % len(good_cycle)][q]:
            continue
        matches.append(j)
    return matches


def main() -> None:
    state_counts = (2, 2, 2, 2, 2, 10)
    n = len(state_counts)
    pivots = [i for i in range(n) if state_counts[(i - 1) % n] == 2 and state_counts[(i + 1) % n] == 2]
    total_cycles = 0
    total_steps = 0
    failures = 0

    for cycle, movers in enumerate_good_cycles(state_counts, max_cycles=50, time_limit=10.0):
        hits = hk_last_instances(movers, n, pivots)
        if not hits:
            continue
        total_cycles += 1
        bad_cfgs, bad_movers = extract_bad_cycle(cycle, movers, state_counts)
        all_good = True
        for k in range(len(bad_cfgs)):
            total_steps += 1
            matches = hentry_exists_for_step(cycle, bad_cfgs, bad_movers, k)
            if not matches:
                failures += 1
                all_good = False
                print(f"\nFAIL cycle#{total_cycles} step k={k} q={bad_movers[k]}")
                print(f"  bad cfg={bad_cfgs[k]}")
                print(f"  bad next q={bad_cfgs[(k+1)%len(bad_cfgs)][bad_movers[k]]}")
                break
        if all_good:
            print(f"cycle#{total_cycles}: hentryCore existential holds at all {len(bad_cfgs)} bad-cycle steps")

    print(f"\nhk_last_cycles={total_cycles} bad_cycle_steps={total_steps} failures={failures}")


if __name__ == "__main__":
    main()
