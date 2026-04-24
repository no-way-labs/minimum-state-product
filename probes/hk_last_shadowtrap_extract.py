#!/usr/bin/env python3
from __future__ import annotations

import os
import sys
import argparse
from collections import defaultdict
from math import prod

ROOT = os.path.dirname(os.path.dirname(__file__))
GPT_SCRIPTS = os.path.join(ROOT, "gpt", "scripts")
sys.path.insert(0, GPT_SCRIPTS)

from p2_good_cycle_search import enumerate_good_cycles  # type: ignore
from p2_cycle_screen import forced_rule_map  # type: ignore
from p2_completion_search import screening_data  # type: ignore


def local_five(t: int, n: int) -> set[int]:
    return {(t - 2) % n, (t - 1) % n, t % n, (t + 1) % n, (t + 2) % n}


def hk_last_instances(movers: tuple[int, ...], state_counts: tuple[int, ...]) -> list[tuple[int, int]]:
    n = len(state_counts)
    pivots = [
        i for i in range(n)
        if state_counts[(i - 1) % n] == 2 and state_counts[(i + 1) % n] == 2
    ]
    hits: list[tuple[int, int]] = []
    for t in pivots:
        outside = [idx for idx, mover in enumerate(movers) if mover not in local_five(t, n)]
        if outside and outside[-1] + 1 == len(movers):
            hits.append((t, outside[-1]))
    return hits


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


def pick_target_multiset(n: int) -> tuple[int, ...]:
    best = None
    best_hits = -1
    limit = 4 * (3 ** (n - 2))
    for ms in subthreshold_multisets(n):
        if not hk_last_instances((0,) * n, ms) and not any(ms[(i - 1) % n] == 2 and ms[(i + 1) % n] == 2 for i in range(n)):
            continue
        hits = 0
        for cycle, movers in enumerate_good_cycles(ms, max_cycles=50, time_limit=2.0):
            hits += len(hk_last_instances(movers, ms))
        if hits > best_hits:
            best_hits = hits
            best = ms
    if best is None:
        raise RuntimeError(f"no target multiset found for n={n} below {limit}")
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

        component: list[int] = []
        while True:
            top = stack.pop()
            on_stack.remove(top)
            component.append(top)
            if top == node:
                break
        components.append(component)

    for node in range(len(adjacency)):
        if indices[node] == -1:
            strongconnect(node)
    return components


def find_simple_cycle_in_scc(scc_nodes: set[int], edges: dict[int, list[tuple[int, int]]]) -> list[tuple[int, int]]:
    start = next(iter(scc_nodes))
    seen_step: dict[int, int] = {}
    path: list[tuple[int, int]] = []
    node = start
    while True:
        if node in seen_step:
            return path[seen_step[node]:]
        seen_step[node] = len(path)
        internal = [(proc, dst) for proc, dst in edges[node] if dst in scc_nodes]
        if not internal:
            raise RuntimeError("SCC node had no internal edge")
        proc, dst = internal[0]
        path.append((node, proc))
        node = dst


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=6)
    args = parser.parse_args()

    state_counts = pick_target_multiset(args.n)
    print(f"target state_counts={state_counts}")

    chosen_cycle = None
    chosen_movers = None
    chosen_hit = None
    for cycle, movers in enumerate_good_cycles(state_counts, max_cycles=50, time_limit=5.0):
        hits = hk_last_instances(movers, state_counts)
        if hits:
            chosen_cycle = cycle
            chosen_movers = movers
            chosen_hit = hits[0]
            break

    if chosen_cycle is None or chosen_movers is None or chosen_hit is None:
        print("no hk_last witness found in search budget")
        return

    t, k_out = chosen_hit
    print(f"chosen hk_last witness: pivot={t} k_out={k_out} len={len(chosen_cycle)}")
    print(f"movers={chosen_movers}")

    cycle_set = frozenset(chosen_cycle)
    fm = forced_rule_map(chosen_cycle, chosen_movers)
    data = screening_data(state_counts)

    forced_edges: dict[int, list[tuple[int, int]]] = defaultdict(list)
    adjacency: list[list[int]] = [[] for _ in data.configs]
    for idx, config in enumerate(data.configs):
        if config in cycle_set:
            continue
        for processor, key in enumerate(data.config_keys[idx]):
            out_state = fm.get(key)
            if out_state is None or out_state == config[processor]:
                continue
            nxt = list(config)
            nxt[processor] = out_state
            dst = data.index[tuple(nxt)]
            if data.configs[dst] in cycle_set:
                continue
            forced_edges[idx].append((processor, dst))
            adjacency[idx].append(dst)

    sccs = [comp for comp in tarjan_scc(adjacency) if len(comp) > 1]
    print(f"nontrivial off-cycle SCCs={len(sccs)}")
    if not sccs:
        print("no bad SCC found")
        return

    scc = sccs[0]
    scc_set = set(scc)
    print(f"chosen SCC size={len(scc)}")
    cycle = find_simple_cycle_in_scc(scc_set, forced_edges)
    print(f"extracted directed cycle length={len(cycle)}")
    print("candidate ShadowTrap configs / chosen processors:")
    for node, proc in cycle:
        print(f"  cfg={data.configs[node]}  --P{proc}-->")
    first_node, _ = cycle[0]
    print(f"  back to cfg={data.configs[first_node]}")


if __name__ == "__main__":
    main()
