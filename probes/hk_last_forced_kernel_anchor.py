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


def first_hk_last_witness(ms: tuple[int, ...]):
    n = len(ms)
    for cycle, movers in enumerate_good_cycles(ms, max_cycles=30, time_limit=6.0):
        hits = hk_last_instances(movers, n, pivots(ms))
        if hits:
            return cycle, movers, hits[0]
    return None


def first_bad_cfg(cycle, movers, ms):
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
    return data.configs[scc[0]]


def main() -> None:
    for n in range(6, 10):
        ms = tuple(2 for _ in range(n))
        witness = first_hk_last_witness(ms)
        if witness is None:
            print(f"n={n}: no hk_last witness found")
            continue
        cycle, movers, hit = witness
        bad0 = first_bad_cfg(cycle, movers, ms)
        ranked = []
        for idx, cfg in enumerate(cycle):
            diff = tuple(i for i, (a, b) in enumerate(zip(cfg, bad0)) if a != b)
            ranked.append((len(diff), idx, diff, cfg))
        ranked.sort()
        print(f"\n=== n={n} ===")
        print(f"movers={movers}")
        print(f"hit={hit}")
        print(f"bad0={bad0}")
        for dist, idx, diff, cfg in ranked[:6]:
            mark = ""
            if idx == n:
                mark += " midpoint"
            if idx == 0:
                mark += " start"
            print(f"  idx={idx:2d} dist={dist} diff={diff}{mark} cfg={cfg}")


if __name__ == "__main__":
    main()
