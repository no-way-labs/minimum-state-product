#!/usr/bin/env python3
from __future__ import annotations

import argparse
import itertools
import os
import sys
from collections import defaultdict
from math import prod

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


def pivots(ms: tuple[int, ...]) -> list[int]:
    n = len(ms)
    return [i for i in range(n) if ms[(i - 1) % n] == 2 and ms[(i + 1) % n] == 2]


def subthreshold_multisets(n: int) -> list[tuple[int, ...]]:
    limit = 4 * (3 ** (n - 2))
    out: list[tuple[int, ...]] = []

    def rec(pos: int, last: int, cur_prod: int, cur: list[int]) -> None:
        if pos == n:
            if cur_prod < limit:
                out.append(tuple(cur))
            return
        maxv = limit // cur_prod
        for v in range(last, maxv + 1):
            if cur_prod * v >= limit:
                break
            cur.append(v)
            rec(pos + 1, v, cur_prod * v, cur)
            cur.pop()

    rec(0, 2, 1, [])
    return out


def pick_target(n: int) -> tuple[int, ...]:
    best = None
    best_hits = -1
    for ms in subthreshold_multisets(n):
        hits = 0
        for cycle, movers in enumerate_good_cycles(ms, max_cycles=50, time_limit=2.0):
            hits += len(hk_last_instances(movers, len(ms), pivots(ms)))
        if hits > best_hits:
            best = ms
            best_hits = hits
    assert best is not None
    print(f"picked target multiset={best} product={prod(best)} hk_last_hits={best_hits}")
    return best


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
    return bad_cfgs


def smallest_separating_projection(good_cfgs, bad_cfgs):
    n = len(good_cfgs[0])
    for r in range(1, min(5, n + 1)):
        for coords in itertools.combinations(range(n), r):
            good_proj = {tuple(cfg[i] for i in coords) for cfg in good_cfgs}
            bad_proj = {tuple(cfg[i] for i in coords) for cfg in bad_cfgs}
            if good_proj.isdisjoint(bad_proj):
                return coords, good_proj, bad_proj
    return None, None, None


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, nargs="+", default=[6, 7, 8])
    args = parser.parse_args()

    for n in args.n:
        ms = pick_target(n)
        chosen = None
        for cycle, movers in enumerate_good_cycles(ms, max_cycles=50, time_limit=5.0):
            if hk_last_instances(movers, n, pivots(ms)):
                chosen = (cycle, movers)
                break
        assert chosen is not None
        cycle, movers = chosen
        bad_cfgs = extract_bad_cycle(cycle, movers, ms)
        coords, good_proj, bad_proj = smallest_separating_projection(cycle, bad_cfgs)
        print(f"\n=== n={n} ===")
        print(f"good_len={len(cycle)} bad_len={len(bad_cfgs)}")
        print(f"binary_only_bad={all(v in (0,1) for cfg in bad_cfgs for v in cfg)}")
        print(f"smallest separating coords={coords}")
        if coords is not None:
            print(f"  sample good projections={sorted(list(good_proj))[:8]}")
            print(f"  sample bad projections={sorted(list(bad_proj))[:8]}")


if __name__ == "__main__":
    main()
