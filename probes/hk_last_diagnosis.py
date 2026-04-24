#!/usr/bin/env python3
from __future__ import annotations

import os
import sys
import time
from collections import Counter
from dataclasses import dataclass
from math import prod

ROOT = os.path.dirname(os.path.dirname(__file__))
GPT_SCRIPTS = os.path.join(ROOT, "gpt", "scripts")
sys.path.insert(0, GPT_SCRIPTS)

from p2_good_cycle_search import enumerate_good_cycles  # type: ignore
from p2_cycle_screen import forced_rule_map  # type: ignore
from p2_completion_search import screening_data  # type: ignore
from p2_smt_completion import solve_cycle_with_smt  # type: ignore


def pivots_with_binary_neighbors(state_counts: tuple[int, ...]) -> list[int]:
    n = len(state_counts)
    return [
        i for i in range(n)
        if state_counts[(i - 1) % n] == 2 and state_counts[(i + 1) % n] == 2
    ]


def local_five(t: int, n: int) -> set[int]:
    return {(t - 2) % n, (t - 1) % n, t % n, (t + 1) % n, (t + 2) % n}


def hk_last_instances(movers: tuple[int, ...], state_counts: tuple[int, ...]) -> list[tuple[int, int]]:
    n = len(state_counts)
    hits: list[tuple[int, int]] = []
    for t in pivots_with_binary_neighbors(state_counts):
        local = local_five(t, n)
        outside = [idx for idx, mover in enumerate(movers) if mover not in local]
        if not outside:
            continue
        k_out = outside[-1]
        if k_out + 1 == len(movers):
            hits.append((t, k_out))
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


@dataclass
class FatalInfo:
    kind: str
    detail: str


def fatal_forced_cycle_details(
    state_counts: tuple[int, ...],
    cycle_set: frozenset[tuple[int, ...]],
    forced_map: dict,
) -> FatalInfo | None:
    data = screening_data(state_counts)
    forced_edges: list[list[tuple[int, int]]] = [[] for _ in data.configs]

    for idx, config in enumerate(data.configs):
        if config in cycle_set:
            continue
        for processor, key in enumerate(data.config_keys[idx]):
            out_state = forced_map.get(key)
            if out_state is None or out_state == config[processor]:
                continue
            nxt = list(config)
            nxt[processor] = out_state
            forced_edges[idx].append((processor, data.index[tuple(nxt)]))

    adjacency = [[dst for _, dst in edges if data.configs[dst] not in cycle_set] for edges in forced_edges]
    required = set(range(len(state_counts)))

    for scc in tarjan_scc(adjacency):
        if len(scc) <= 1:
            continue
        scc_set = set(scc)
        seen_processors = set()
        for node in scc:
            internal_edges = [(processor, dst) for processor, dst in forced_edges[node] if dst in scc_set]
            if len(forced_edges[node]) != 1 or len(internal_edges) != 1:
                return FatalInfo(
                    kind="forced_recurrent_component",
                    detail=f"branching/ambiguous forced SCC size={len(scc)} node={data.configs[node]}",
                )
            seen_processors.add(internal_edges[0][0])
        if seen_processors != required:
            missing = sorted(required - seen_processors)
            return FatalInfo(
                kind="forced_recurrent_component",
                detail=f"closed forced SCC size={len(scc)} missing processors={missing}",
            )
    return None


def pick_target_multiset() -> tuple[int, ...]:
    best: tuple[int, ...] | None = None
    best_hits = -1
    for state_counts in subthreshold_multisets(6):
        if not pivots_with_binary_neighbors(state_counts):
            continue
        hits = 0
        for cycle, movers in enumerate_good_cycles(state_counts, max_cycles=50, time_limit=2.0):
            hits += len(hk_last_instances(movers, state_counts))
        if hits > best_hits:
            best = state_counts
            best_hits = hits
    assert best is not None
    print(f"picked target multiset={best} product={prod(best)} hk_last_hits={best_hits}")
    return best


def main() -> None:
    state_counts = pick_target_multiset()
    pivots = pivots_with_binary_neighbors(state_counts)
    print(f"pivots={pivots}")

    kill_counter: Counter[str] = Counter()
    pair_counter: Counter[tuple[int, int, int]] = Counter()
    analyzed = 0

    started = time.time()
    for cycle_idx, (cycle, movers) in enumerate(enumerate_good_cycles(state_counts, max_cycles=50, time_limit=10.0), start=1):
        hits = hk_last_instances(movers, state_counts)
        if not hits:
            continue
        cycle_set = frozenset(cycle)
        fm = forced_rule_map(cycle, movers)
        fatal = fatal_forced_cycle_details(state_counts, cycle_set, fm)
        if fatal is not None:
            for t, k_out in hits:
                analyzed += 1
                kill_counter[fatal.kind] += 1
                pair_counter[(t, movers[k_out], movers[0])] += 1
                print(f"\ncycle {cycle_idx} hk_last at t={t} k_out={k_out} len={len(cycle)}")
                print(f"  movers[k_out]={movers[k_out]} movers[0]={movers[0]}")
                print(f"  killed_by={fatal.kind}: {fatal.detail}")
            continue

        result = solve_cycle_with_smt(state_counts, cycle, movers, timeout_ms=5000)
        for t, k_out in hits:
            analyzed += 1
            if result.found:
                kind = "valid_completion"
                detail = result.message
            elif "propagation proves" in result.message:
                kind = "propagation"
                detail = result.message
            elif "SMT encoding proves" in result.message:
                kind = "smt_unsat"
                detail = result.message
            else:
                kind = "other"
                detail = result.message
            kill_counter[kind] += 1
            pair_counter[(t, movers[k_out], movers[0])] += 1
            print(f"\ncycle {cycle_idx} hk_last at t={t} k_out={k_out} len={len(cycle)}")
            print(f"  movers[k_out]={movers[k_out]} movers[0]={movers[0]}")
            print(f"  killed_by={kind}: {detail}")

    print(f"\nanalyzed_hk_last_instances={analyzed} elapsed={time.time() - started:.2f}s")
    print("kill summary:")
    for key, count in kill_counter.most_common():
        print(f"  {key}: {count}")
    print("pair summary (pivot, mover[k_out], mover[0]):")
    for key, count in pair_counter.most_common():
        print(f"  {key}: {count}")


if __name__ == "__main__":
    main()
