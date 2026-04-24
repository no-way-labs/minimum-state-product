#!/usr/bin/env python3
from __future__ import annotations

import os
import sys
from collections import defaultdict
from itertools import combinations

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


def basin_and_good(cycle, movers, ms):
    n = len(ms)
    cycle_set = frozenset(cycle)
    fm = forced_rule_map(cycle, movers)
    data = screening_data(ms)
    outgoing_bad: list[list[int]] = [[] for _ in data.configs]
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

    sccs = [comp for comp in tarjan_scc(outgoing_bad) if len(comp) > 1]
    reach_bad_scc = set().union(*map(set, sccs)) if sccs else set()
    changed = True
    while changed:
        changed = False
        for idx, dsts in enumerate(outgoing_bad):
            if idx in reach_bad_scc:
                continue
            if any(dst in reach_bad_scc for dst in dsts):
                reach_bad_scc.add(idx)
                changed = True

    basin = [data.configs[idx] for idx in sorted(reach_bad_scc)]
    return list(cycle), basin


def smallest_separating_projection(good, bad, n):
    for r in range(1, min(5, n + 1)):
        for coords in combinations(range(n), r):
            g = {tuple(cfg[i] for i in coords) for cfg in good}
            b = {tuple(cfg[i] for i in coords) for cfg in bad}
            if g.isdisjoint(b):
                return coords, g, b
    return None, None, None


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
        good, basin = basin_and_good(cycle, movers, ms)
        coords, gproj, bproj = smallest_separating_projection(good, basin, n)
        print(f"\n=== non-sweep witness {seen} ===")
        print(f"movers={movers}")
        print(f"hits={hits}")
        print(f"good_size={len(good)} basin_size={len(basin)}")
        print(f"smallest separating coords={coords}")
        if coords is not None:
            print(f"  good projections={sorted(list(gproj))[:12]}")
            print(f"  basin projections={sorted(list(bproj))[:12]}")
        if seen >= 5:
            break


if __name__ == "__main__":
    main()
