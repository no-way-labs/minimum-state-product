#!/usr/bin/env python3
from __future__ import annotations

import os
import sys
from collections import defaultdict, deque, Counter

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
    outgoing: dict[int, list[int]] = defaultdict(list)
    outgoing_bad: list[list[int]] = [[] for _ in data.configs]
    reverse_all: list[list[int]] = [[] for _ in data.configs]
    cycle_indices = {data.index[cfg] for cfg in cycle}

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
            outgoing[idx].append(dst)
            reverse_all[dst].append(idx)
            if data.configs[dst] not in cycle_set:
                outgoing_bad[idx].append(dst)

    # shortest distance to the good cycle, when one exists
    dist_good = {}
    q = deque()
    for idx in cycle_indices:
        dist_good[idx] = 0
        q.append(idx)
    while q:
        v = q.popleft()
        for src in reverse_all[v]:
            if src not in dist_good:
                dist_good[src] = dist_good[v] + 1
                q.append(src)

    sccs = [comp for comp in tarjan_scc(outgoing_bad) if len(comp) > 1]
    bad_scc_nodes = set().union(*map(set, sccs)) if sccs else set()

    # can reach a bad SCC?
    reach_bad_scc = set(bad_scc_nodes)
    changed = True
    while changed:
        changed = False
        for idx, dsts in enumerate(outgoing_bad):
            if idx in reach_bad_scc:
                continue
            if any(dst in reach_bad_scc for dst in dsts):
                reach_bad_scc.add(idx)
                changed = True

    bad_nodes = [idx for idx, cfg in enumerate(data.configs) if cfg not in cycle_set]
    stats = Counter()
    sample = []
    for idx in bad_nodes:
        to_good = idx in dist_good
        to_bad_scc = idx in reach_bad_scc
        key = (to_good, to_bad_scc)
        stats[key] += 1
        if len(sample) < 8:
            sample.append((data.configs[idx], to_good, dist_good.get(idx), to_bad_scc, len(outgoing[idx])))
    return stats, sample, len(sccs), sorted(len(comp) for comp in sccs)[:8]


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
        stats, sample, nscc, scc_sizes = analyze(cycle, movers, ms)
        print(f"\n=== non-sweep witness {seen} ===")
        print(f"movers={movers}")
        print(f"hits={hits}")
        print(f"off-cycle SCC count={nscc} sizes={scc_sizes}")
        print(f"reachability stats (to_good, to_bad_scc) -> count: {dict(stats)}")
        print("sample bad states:")
        for cfg, to_good, dgood, to_bad_scc, outdeg in sample:
            print(f"  cfg={cfg} to_good={to_good} dist_good={dgood} to_bad_scc={to_bad_scc} outdeg={outdeg}")
        if seen >= 5:
            break


if __name__ == "__main__":
    main()
