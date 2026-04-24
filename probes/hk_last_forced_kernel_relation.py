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


def main() -> None:
    ms = (2,) * 9
    n = len(ms)
    cycle = None
    movers = None
    for gc, mw in enumerate_good_cycles(ms, max_cycles=20, time_limit=6.0):
        if hk_last_instances(mw, n, pivots(ms)):
            cycle = gc
            movers = mw
            break
    if cycle is None or movers is None:
        raise SystemExit("no hk_last witness found")

    cycle_set = frozenset(cycle)
    fm = forced_rule_map(cycle, movers)
    data = screening_data(ms)
    edges: dict[int, list[tuple[int, int]]] = defaultdict(list)
    adjacency: list[list[int]] = [[] for _ in data.configs]
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
    bad0 = data.configs[scc[0]]
    print(f"movers={movers}")
    print(f"bad0={bad0}")

    ranked = []
    for idx, cfg in enumerate(cycle):
        diff = [i for i, (a, b) in enumerate(zip(cfg, bad0)) if a != b]
        ranked.append((len(diff), idx, tuple(diff), cfg))
    ranked.sort()

    print("\nclosest good configs:")
    for dist, idx, diff, cfg in ranked[:8]:
        print(f"  idx={idx:2d} dist={dist} diff={diff} cfg={cfg}")

    print("\ndifference-frequency over whole good cycle:")
    diff_counter = defaultdict(int)
    for _, _, diff, _ in ranked:
        diff_counter[diff] += 1
    for diff, count in sorted(diff_counter.items(), key=lambda kv: (len(kv[0]), kv[0])):
        print(f"  diff={diff} count={count}")


if __name__ == "__main__":
    main()
