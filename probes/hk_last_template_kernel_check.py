#!/usr/bin/env python3
from __future__ import annotations

import os
import sys
from collections import defaultdict, Counter

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


def basin_nodes(cycle, movers, ms):
    cycle_set = frozenset(cycle)
    fm = forced_rule_map(cycle, movers)
    data = screening_data(ms)
    outgoing_bad = [[] for _ in data.configs]
    outgoing_labeled: dict[int, list[tuple[int, int]]] = defaultdict(list)
    bad_indices = [idx for idx, cfg in enumerate(data.configs) if cfg not in cycle_set]
    for idx in bad_indices:
        cfg = data.configs[idx]
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
            outgoing_labeled[idx].append((proc, dst))
    sccs = [comp for comp in tarjan_scc(outgoing_bad) if len(comp) > 1]
    inf = set().union(*map(set, sccs)) if sccs else set()
    changed = True
    while changed:
        changed = False
        for idx in bad_indices:
            if idx in inf:
                continue
            if any(dst in inf for dst in outgoing_bad[idx]):
                inf.add(idx)
                changed = True
    return data, inf, outgoing_labeled


def template_matches(cfg: tuple[int, ...], cycle, movers):
    matches = []
    n = len(cfg)
    for j, gcfg in enumerate(cycle):
        p = movers[j]
        l = (p - 1) % n
        r = (p + 1) % n
        if cfg[l] == gcfg[l] and cfg[p] == gcfg[p] and cfg[r] == gcfg[r]:
            matches.append(j)
    return matches


def main() -> None:
    n = 7
    ms = (2,) * n
    seen = 0
    for cycle, movers in enumerate_good_cycles(ms, max_cycles=80, time_limit=8.0):
        hits = hk_last_instances(movers, n, pivots(ms))
        if not hits:
            continue
        if is_forward_sweep(movers, n) or is_reverse_sweep(movers, n):
            continue
        seen += 1
        data, basin, outgoing = basin_nodes(cycle, movers, ms)
        tmpl_counts = Counter()
        closure_ok = 0
        closure_fail = 0
        step_shift = Counter()
        samples = []
        for idx in sorted(basin):
            cfg = data.configs[idx]
            ms0 = template_matches(cfg, cycle, movers)
            tmpl_counts[len(ms0)] += 1
            if not ms0:
                closure_fail += 1
                continue
            if idx not in outgoing or not outgoing[idx]:
                closure_fail += 1
                continue
            proc, dst = outgoing[idx][0]
            ms1 = template_matches(data.configs[dst], cycle, movers)
            if ms1:
                closure_ok += 1
                for a in ms0[:3]:
                    for b in ms1[:3]:
                        step_shift[(b - a) % len(cycle)] += 1
            else:
                closure_fail += 1
                if len(samples) < 6:
                    samples.append((cfg, ms0, proc, data.configs[dst], ms1))
        print(f"\n=== non-sweep witness {seen} ===")
        print(f"movers={movers}")
        print(f"hits={hits}")
        print(f"basin_size={len(basin)}")
        print(f"template_match_count_distribution={dict(sorted(tmpl_counts.items()))}")
        print(f"closure_ok={closure_ok} closure_fail={closure_fail}")
        print(f"common step shifts={step_shift.most_common(10)}")
        if samples:
            print('sample closure failures:')
            for s in samples:
                print(' ', s)
        if seen >= 5:
            break


if __name__ == "__main__":
    main()
