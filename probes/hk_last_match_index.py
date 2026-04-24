#!/usr/bin/env python3
from __future__ import annotations

import argparse
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


def shadow_perm(n: int, k: int) -> int:
    if k == 0:
        return n - 4
    if k == 1:
        return n - 1
    if k == 2:
        return 0
    if k <= n - 3:
        return k - 2
    if k == n - 2:
        return n - 2
    return n - 3


def shadow_shift(n: int, i: int) -> int:
    if i <= n - 5:
        return n - 2 - i
    if i == n - 4:
        return 0
    if i == n - 3:
        return n + 1
    if i == n - 2:
        return 2
    return 2 * n - 1


def shadow_active(n: int, j: int, d: int) -> bool:
    x = (j + d) % (2 * n)
    return 1 <= x <= n


def local_five(t: int, n: int) -> set[int]:
    return {(t - 2) % n, (t - 1) % n, t, (t + 1) % n, (t + 2) % n}


def pivots(ms: tuple[int, ...]) -> list[int]:
    n = len(ms)
    return [i for i in range(n) if ms[(i - 1) % n] == 2 and ms[(i + 1) % n] == 2]


def hk_last_instances(movers: tuple[int, ...], ms: tuple[int, ...]) -> list[tuple[int, int]]:
    n = len(ms)
    hits = []
    for t in pivots(ms):
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


def pick_target(n: int) -> tuple[int, ...]:
    best = None
    best_hits = -1
    for ms in subthreshold_multisets(n):
        hits = 0
        for cycle, movers in enumerate_good_cycles(ms, max_cycles=50, time_limit=2.0):
            hits += len(hk_last_instances(movers, ms))
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


def extract_bad_cycle(ms: tuple[int, ...]):
    cycle = movers = hit = None
    for c, m in enumerate_good_cycles(ms, max_cycles=50, time_limit=5.0):
        hits = hk_last_instances(m, ms)
        if hits:
            cycle, movers, hit = c, m, hits[0]
            break
    assert cycle is not None and movers is not None and hit is not None
    cycle_set = frozenset(cycle)
    fm = forced_rule_map(cycle, movers)
    data = screening_data(ms)
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
    return cycle, movers, hit, bad_cfgs, bad_movers


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, nargs="+", default=[6, 7, 8])
    args = parser.parse_args()

    for n in args.n:
        ms = pick_target(n)
        good_cycle, good_movers, (t, k_out), bad_cfgs, bad_movers = extract_bad_cycle(ms)
        sigma = [shadow_perm(n, k) for k in range(n)]
        match = next(r for r in range(n) if sigma[r:] + sigma[:r] == list(bad_movers[:n]))
        print(f"\n=== n={n} ===")
        print(f"pivot={t} k_out={k_out} len(good)={len(good_cycle)} len(bad)={len(bad_cfgs)}")
        print(f"rotation={match}")
        ok_all = True
        for k in range(2 * n):
            q = bad_movers[k]
            active = bad_cfgs[k][q] == 1
            j = q + (n if active else 0)
            left = good_cycle[j][(q - 1) % n]
            selfv = good_cycle[j][q]
            right = good_cycle[j][(q + 1) % n]
            next_self = good_cycle[(j + 1) % (2 * n)][q]
            obs_next = bad_cfgs[(k + 1) % (2 * n)][q]
            matches = (bad_cfgs[k][(q - 1) % n] == left and
                       bad_cfgs[k][q] == selfv and
                       bad_cfgs[k][(q + 1) % n] == right and
                       obs_next == next_self)
            if not matches:
                ok_all = False
                print(f"  mismatch at k={k}: q={q} j={j}")
                print(f"    bad triple={(bad_cfgs[k][(q - 1) % n], bad_cfgs[k][q], bad_cfgs[k][(q + 1) % n])}")
                print(f"    good triple={(left, selfv, right)}")
                print(f"    bad next self={obs_next} good next self={next_self}")
                break
        print(f"shadowMatchIndex-style correspondence={ok_all}")


if __name__ == "__main__":
    main()
