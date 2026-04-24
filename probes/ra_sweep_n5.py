#!/usr/bin/env python3
"""Enumerate good Hamiltonian cycles for n=5, ms=(2,2,2,3,3).

The search space is the full configuration graph:
  - vertices: all 72 configurations
  - edges: change exactly one processor to a different local state

A "good cycle" here means a directed Hamiltonian cycle whose induced local
transition table is consistent:
  - the same local context (p, L, S, R) always maps to the same output

If exhaustive DFS does not finish within 3 minutes, the script falls back to
randomized branch-and-propagate sampling, per the task instructions.
"""

from __future__ import annotations

import json
import random
import time
from dataclasses import dataclass
from itertools import product
from typing import Iterable


MS = (2, 2, 2, 3, 3)
N = 5
START_CONFIG = (0, 0, 0, 0, 0)
DFS_TIME_LIMIT_SEC = 180.0
SAMPLE_ATTEMPTS = 20_000
RESULTS_PATH = "ra_sweep_n5_results.json"


@dataclass(frozen=True)
class Edge:
    dst: int
    mover: int
    new_state: int
    assignments: tuple[tuple[int, int], ...]


def local_context(config: tuple[int, ...], proc: int, n: int) -> tuple[int, int, int]:
    return (config[(proc - 1) % n], config[proc], config[(proc + 1) % n])


def first_cycle_in_assigned(
    outgoing: tuple[int, ...],
    edges: tuple[tuple[Edge, ...], ...],
) -> list[int] | None:
    total = len(outgoing)
    globally_seen = [False] * total
    for start in range(total):
        if outgoing[start] == -1 or globally_seen[start]:
            continue
        pos: dict[int, int] = {}
        path: list[int] = []
        cur = start
        while True:
            if outgoing[cur] == -1:
                for node in path:
                    globally_seen[node] = True
                break
            if cur in pos:
                return path[pos[cur] :]
            if globally_seen[cur]:
                for node in path:
                    globally_seen[node] = True
                break
            pos[cur] = len(path)
            path.append(cur)
            cur = edges[cur][outgoing[cur]].dst
    return None


class HamiltonianCycleEnumerator:
    def __init__(self, ms: tuple[int, ...]) -> None:
        self.ms = ms
        self.n = len(ms)
        self.configs = tuple(product(*(range(m) for m in ms)))
        self.config_index = {cfg: idx for idx, cfg in enumerate(self.configs)}
        self.total = len(self.configs)
        self.start_index = self.config_index[START_CONFIG]

        rule_keys: list[tuple[int, int, int, int]] = []
        for proc in range(self.n):
            for left in range(ms[(proc - 1) % self.n]):
                for self_val in range(ms[proc]):
                    for right in range(ms[(proc + 1) % self.n]):
                        rule_keys.append((proc, left, self_val, right))
        self.rule_keys = tuple(rule_keys)
        self.rule_index = {key: idx for idx, key in enumerate(self.rule_keys)}

        all_edges: list[tuple[Edge, ...]] = []
        for src_idx, config in enumerate(self.configs):
            src_edges: list[Edge] = []
            for proc in range(self.n):
                for new_state in range(ms[proc]):
                    if new_state == config[proc]:
                        continue
                    nxt = list(config)
                    nxt[proc] = new_state
                    dst_idx = self.config_index[tuple(nxt)]
                    assignments = []
                    for other in range(self.n):
                        key = self.rule_index[(other, *local_context(config, other, self.n))]
                        required = new_state if other == proc else config[other]
                        assignments.append((key, required))
                    src_edges.append(
                        Edge(
                            dst=dst_idx,
                            mover=proc,
                            new_state=new_state,
                            assignments=tuple(assignments),
                        )
                    )
            all_edges.append(tuple(src_edges))
        self.edges = tuple(all_edges)

        self.deadline = 0.0
        self.stats = {
            "search_mode": "exhaustive",
            "nodes": 0,
            "forced_assignments": 0,
            "branch_choices": 0,
            "best_assigned": 0,
            "timed_out": False,
            "sampling_attempts": 0,
            "sampling_successes": 0,
        }

    def candidate_valid(
        self,
        src: int,
        edge_idx: int,
        rules: tuple[int, ...],
        incoming: tuple[int, ...],
        outgoing: tuple[int, ...],
    ) -> bool:
        edge = self.edges[src][edge_idx]
        incumbent = incoming[edge.dst]
        if incumbent != -1 and incumbent != src:
            return False
        if outgoing[src] != -1 and outgoing[src] != edge_idx:
            return False
        for key_idx, out_value in edge.assignments:
            current = rules[key_idx]
            if current != -1 and current != out_value:
                return False
        return True

    def apply_edge(
        self,
        src: int,
        edge_idx: int,
        rules: tuple[int, ...],
        incoming: tuple[int, ...],
        outgoing: tuple[int, ...],
    ) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]] | None:
        edge = self.edges[src][edge_idx]
        if outgoing[src] != -1 and outgoing[src] != edge_idx:
            return None
        if incoming[edge.dst] != -1 and incoming[edge.dst] != src:
            return None

        next_rules = list(rules)
        for key_idx, out_value in edge.assignments:
            current = next_rules[key_idx]
            if current != -1 and current != out_value:
                return None
            next_rules[key_idx] = out_value

        next_incoming = list(incoming)
        next_outgoing = list(outgoing)
        next_incoming[edge.dst] = src
        next_outgoing[src] = edge_idx
        return (tuple(next_rules), tuple(next_incoming), tuple(next_outgoing))

    def compute_masks_and_supports(
        self,
        rules: tuple[int, ...],
        incoming: tuple[int, ...],
        outgoing: tuple[int, ...],
    ) -> tuple[list[int], list[list[tuple[int, int]]]] | None:
        masks = [0] * self.total
        supports: list[list[tuple[int, int]]] = [[] for _ in range(self.total)]
        for src in range(self.total):
            mask = 0
            if outgoing[src] != -1:
                edge_idx = outgoing[src]
                if not self.candidate_valid(src, edge_idx, rules, incoming, outgoing):
                    return None
                mask = 1 << edge_idx
                supports[self.edges[src][edge_idx].dst].append((src, edge_idx))
            else:
                for edge_idx in range(len(self.edges[src])):
                    if self.candidate_valid(src, edge_idx, rules, incoming, outgoing):
                        mask |= 1 << edge_idx
                        supports[self.edges[src][edge_idx].dst].append((src, edge_idx))
                if mask == 0:
                    return None
            masks[src] = mask
        return masks, supports

    def propagate(
        self,
        rules: tuple[int, ...],
        incoming: tuple[int, ...],
        outgoing: tuple[int, ...],
    ) -> tuple[
        tuple[int, ...],
        tuple[int, ...],
        tuple[int, ...],
        list[int],
        list[list[tuple[int, int]]],
    ] | None:
        while True:
            computed = self.compute_masks_and_supports(rules, incoming, outgoing)
            if computed is None:
                return None
            masks, supports = computed

            assigned_cycle = first_cycle_in_assigned(outgoing, self.edges)
            if assigned_cycle is not None and len(assigned_cycle) < self.total:
                return None

            forced: list[tuple[int, int]] = []

            for dst in range(self.total):
                if incoming[dst] != -1:
                    continue
                if not supports[dst]:
                    return None
                if len(supports[dst]) == 1:
                    forced.append(supports[dst][0])

            for src in range(self.total):
                if outgoing[src] != -1:
                    continue
                mask = masks[src]
                if mask & (mask - 1) == 0:
                    forced.append((src, mask.bit_length() - 1))

            if not forced:
                return rules, incoming, outgoing, masks, supports

            seen: set[tuple[int, int]] = set()
            for src, edge_idx in forced:
                if (src, edge_idx) in seen:
                    continue
                seen.add((src, edge_idx))
                updated = self.apply_edge(src, edge_idx, rules, incoming, outgoing)
                if updated is None:
                    return None
                rules, incoming, outgoing = updated
                self.stats["forced_assignments"] += 1

    def extract_cycle(self, outgoing: tuple[int, ...]) -> tuple[list[tuple[int, ...]], list[int]]:
        configs: list[tuple[int, ...]] = []
        movers: list[int] = []
        seen: set[int] = set()
        cur = self.start_index
        while cur not in seen:
            seen.add(cur)
            configs.append(self.configs[cur])
            edge = self.edges[cur][outgoing[cur]]
            movers.append(edge.mover)
            cur = edge.dst
        if cur != self.start_index or len(configs) != self.total:
            raise ValueError("assignment is not a Hamiltonian cycle through START_CONFIG")
        return configs, movers

    def summarize_cycle(self, outgoing: tuple[int, ...]) -> dict:
        configs, movers = self.extract_cycle(outgoing)
        return analyze_cycle(configs, movers, self.ms)

    def enumerate_exhaustive(self, time_limit_sec: float) -> list[dict]:
        self.deadline = time.monotonic() + time_limit_sec
        initial_rules = tuple([-1] * len(self.rule_keys))
        initial_incoming = tuple([-1] * self.total)
        initial_outgoing = tuple([-1] * self.total)
        found: list[dict] = []

        def dfs(
            rules: tuple[int, ...],
            incoming: tuple[int, ...],
            outgoing: tuple[int, ...],
        ) -> None:
            if time.monotonic() > self.deadline:
                self.stats["timed_out"] = True
                raise TimeoutError

            self.stats["nodes"] += 1
            propagated = self.propagate(rules, incoming, outgoing)
            if propagated is None:
                return

            rules_p, incoming_p, outgoing_p, masks, supports = propagated
            assigned = sum(1 for value in outgoing_p if value != -1)
            if assigned > self.stats["best_assigned"]:
                self.stats["best_assigned"] = assigned

            if assigned == self.total:
                cycle = first_cycle_in_assigned(outgoing_p, self.edges)
                if cycle is not None and len(cycle) == self.total:
                    found.append(self.summarize_cycle(outgoing_p))
                return

            branch_src = -1
            branch_mask = 0
            best_count = 10**9
            for src in range(self.total):
                if outgoing_p[src] != -1:
                    continue
                count = masks[src].bit_count()
                if count < best_count:
                    best_count = count
                    branch_src = src
                    branch_mask = masks[src]
                    if count == 2:
                        break

            candidates = [edge_idx for edge_idx in range(len(self.edges[branch_src])) if branch_mask & (1 << edge_idx)]
            candidates.sort(
                key=lambda edge_idx: (
                    len(supports[self.edges[branch_src][edge_idx].dst]),
                    self.edges[branch_src][edge_idx].mover,
                    self.edges[branch_src][edge_idx].dst,
                )
            )

            for edge_idx in candidates:
                self.stats["branch_choices"] += 1
                updated = self.apply_edge(branch_src, edge_idx, rules_p, incoming_p, outgoing_p)
                if updated is None:
                    continue
                dfs(*updated)

        dfs(initial_rules, initial_incoming, initial_outgoing)
        return found

    def sample_random(self, attempts: int) -> list[dict]:
        self.stats["search_mode"] = "sampling"
        rng = random.Random(0)
        seen: set[tuple[tuple[int, ...], ...]] = set()
        found: list[dict] = []
        initial_rules = tuple([-1] * len(self.rule_keys))
        initial_incoming = tuple([-1] * self.total)
        initial_outgoing = tuple([-1] * self.total)

        for _ in range(attempts):
            self.stats["sampling_attempts"] += 1
            rules = initial_rules
            incoming = initial_incoming
            outgoing = initial_outgoing

            while True:
                propagated = self.propagate(rules, incoming, outgoing)
                if propagated is None:
                    break
                rules, incoming, outgoing, masks, supports = propagated
                assigned = sum(1 for value in outgoing if value != -1)
                if assigned > self.stats["best_assigned"]:
                    self.stats["best_assigned"] = assigned
                if assigned == self.total:
                    cycle = first_cycle_in_assigned(outgoing, self.edges)
                    if cycle is not None and len(cycle) == self.total:
                        configs, _ = self.extract_cycle(outgoing)
                        key = tuple(configs)
                        if key not in seen:
                            seen.add(key)
                            found.append(self.summarize_cycle(outgoing))
                        self.stats["sampling_successes"] += 1
                    break

                branch_src = -1
                branch_mask = 0
                best_count = 10**9
                for src in range(self.total):
                    if outgoing[src] != -1:
                        continue
                    count = masks[src].bit_count()
                    if count < best_count:
                        best_count = count
                        branch_src = src
                        branch_mask = masks[src]
                candidates = [edge_idx for edge_idx in range(len(self.edges[branch_src])) if branch_mask & (1 << edge_idx)]
                candidates.sort(
                    key=lambda edge_idx: (
                        len(supports[self.edges[branch_src][edge_idx].dst]),
                        self.edges[branch_src][edge_idx].mover,
                        self.edges[branch_src][edge_idx].dst,
                    )
                )
                edge_idx = rng.choice(candidates)
                updated = self.apply_edge(branch_src, edge_idx, rules, incoming, outgoing)
                if updated is None:
                    break
                rules, incoming, outgoing = updated

        return found


def direction_weight(cur: int, nxt: int, n: int) -> int:
    if nxt == (cur + 1) % n:
        return 1
    if nxt == (cur - 1) % n:
        return -1
    return 0


def firing_gaps(fire_steps: list[int], cycle_len: int) -> list[tuple[int, int, int]]:
    gaps = []
    for idx, start in enumerate(fire_steps):
        end = fire_steps[(idx + 1) % len(fire_steps)]
        gap = (end - start) % cycle_len
        if gap == 0:
            gap = cycle_len
        gaps.append((start, end, gap))
    return gaps


def entry_conflict_details(
    configs: list[tuple[int, ...]],
    movers: list[int],
    ms: tuple[int, ...],
) -> dict[int, list[list[int]]]:
    details: dict[int, list[list[int]]] = {}
    n = len(ms)
    for proc in range(n):
        mover_ctx = set()
        nonmover_ctx = set()
        for step, config in enumerate(configs):
            ctx = local_context(config, proc, n)
            if movers[step] == proc:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        overlap = mover_ctx & nonmover_ctx
        if overlap:
            details[proc] = [list(ctx) for ctx in sorted(overlap)]
    return details


def analyze_cycle(
    configs: list[tuple[int, ...]],
    movers: list[int],
    ms: tuple[int, ...],
) -> dict:
    n = len(ms)
    cycle_len = len(movers)
    conflicts = entry_conflict_details(configs, movers, ms)
    fire_steps = [step for step, mover in enumerate(movers) if mover == 1]
    fire_count = len(fire_steps)
    isolated = all(movers[(step + 1) % cycle_len] != 1 for step in fire_steps)
    total_displacement = sum(direction_weight(movers[step], movers[(step + 1) % cycle_len], n) for step in range(cycle_len))
    is_sweep = abs(total_displacement) >= 2 * n

    proc1 = {
        "fireCount": fire_count,
        "isolated": isolated,
        "totalDisplacement": total_displacement,
        "isSweep": is_sweep,
        "minGap": None,
        "gapPair": None,
        "J": None,
        "K": None,
        "oddParity": None,
        "dispatchable": None,
        "nonDispatchable": None,
    }

    if isolated and is_sweep and fire_count >= 2:
        gaps = firing_gaps(fire_steps, cycle_len)
        min_gap = min(gap for _, _, gap in gaps)
        gap_pair = next(item for item in gaps if item[2] == min_gap)
        start, end, gap = gap_pair
        interior_steps = [((start + offset) % cycle_len) for offset in range(1, gap)]
        j_count = sum(1 for step in interior_steps if movers[step] == 0)
        k_count = sum(1 for step in interior_steps if movers[step] == 2)
        odd_parity = not (j_count % 2 == 0 and k_count % 2 == 0)
        dispatchable = (
            (j_count % 2 == 0 and k_count % 2 == 0)
            or (j_count >= 2 and k_count == 0)
            or (j_count == 0 and k_count >= 2)
        )
        proc1.update(
            {
                "minGap": min_gap,
                "gapPair": [start, end],
                "J": j_count,
                "K": k_count,
                "oddParity": odd_parity,
                "dispatchable": dispatchable,
                "nonDispatchable": not dispatchable,
            }
        )

    return {
        "startConfig": list(configs[0]),
        "length": cycle_len,
        "moverWord": movers,
        "hasEntryConflict": bool(conflicts),
        "entryConflictDetails": {str(proc): overlaps for proc, overlaps in conflicts.items()},
        "proc1": proc1,
        "configs": [list(cfg) for cfg in configs],
    }


def aggregate_counts(cycles: Iterable[dict]) -> dict[str, int]:
    cycles = list(cycles)
    total = len(cycles)
    with_ec = sum(1 for cycle in cycles if cycle["hasEntryConflict"])
    isolated = sum(1 for cycle in cycles if cycle["proc1"]["isolated"])
    sweep_isolated = sum(1 for cycle in cycles if cycle["proc1"]["isolated"] and cycle["proc1"]["isSweep"])
    sweep_isolated_with_gap = sum(
        1
        for cycle in cycles
        if cycle["proc1"]["isolated"] and cycle["proc1"]["isSweep"] and cycle["proc1"]["minGap"] is not None
    )
    odd = sum(1 for cycle in cycles if cycle["proc1"]["oddParity"] is True)
    even = sum(1 for cycle in cycles if cycle["proc1"]["oddParity"] is False)
    dispatchable = sum(1 for cycle in cycles if cycle["proc1"]["oddParity"] is True and cycle["proc1"]["dispatchable"] is True)
    non_dispatchable = sum(
        1 for cycle in cycles if cycle["proc1"]["oddParity"] is True and cycle["proc1"]["nonDispatchable"] is True
    )
    return {
        "goodCycles": total,
        "hasEntryConflict": with_ec,
        "noEntryConflict": total - with_ec,
        "proc1Isolated": isolated,
        "proc1NotIsolated": total - isolated,
        "proc1SweepAndIsolated": sweep_isolated,
        "proc1SweepAndIsolatedWithMinGap": sweep_isolated_with_gap,
        "proc1SweepAndIsolatedOddParity": odd,
        "proc1SweepAndIsolatedEvenParity": even,
        "proc1SweepAndIsolatedOddDispatchable": dispatchable,
        "proc1SweepAndIsolatedOddNonDispatchable": non_dispatchable,
    }


def main() -> None:
    enumerator = HamiltonianCycleEnumerator(MS)
    started = time.monotonic()

    try:
        cycles = enumerator.enumerate_exhaustive(DFS_TIME_LIMIT_SEC)
    except TimeoutError:
        cycles = enumerator.sample_random(SAMPLE_ATTEMPTS)

    elapsed = time.monotonic() - started
    counts_all = aggregate_counts(cycles)
    counts_no_ec = aggregate_counts([cycle for cycle in cycles if not cycle["hasEntryConflict"]])
    sorry_branch = [cycle for cycle in cycles if cycle["proc1"]["oddParity"] is True and cycle["proc1"]["nonDispatchable"] is True]

    results = {
        "n": N,
        "ms": list(MS),
        "graph": {
            "configCount": enumerator.total,
            "directedEdgeCount": sum(len(src_edges) for src_edges in enumerator.edges),
            "undirectedEdgeCount": sum(len(src_edges) for src_edges in enumerator.edges) // 2,
            "perConfigDegree": len(enumerator.edges[0]),
            "ruleKeyCount": len(enumerator.rule_keys),
        },
        "search": {
            **enumerator.stats,
            "elapsedSec": elapsed,
            "timeLimitSec": DFS_TIME_LIMIT_SEC,
        },
        "countsAllCycles": counts_all,
        "countsNoEntryConflictSubset": counts_no_ec,
        "sorryBranchCount": len(sorry_branch),
        "sorryBranchCycles": sorry_branch,
        "cycleSummaries": cycles,
    }

    with open(RESULTS_PATH, "w", encoding="utf-8") as fh:
        json.dump(results, fh, indent=2)

    print(f"n={N}, ms={MS}")
    print("Config graph:")
    print(f"  configs={results['graph']['configCount']}")
    print(f"  directed_edges={results['graph']['directedEdgeCount']}")
    print(f"  undirected_edges={results['graph']['undirectedEdgeCount']}")
    print(f"  degree={results['graph']['perConfigDegree']}")
    print(f"  rule_keys={results['graph']['ruleKeyCount']}")
    print("Search:")
    print(f"  mode={results['search']['search_mode']}")
    print(f"  elapsed_sec={results['search']['elapsedSec']:.6f}")
    print(f"  nodes={results['search']['nodes']}")
    print(f"  forced_assignments={results['search']['forced_assignments']}")
    print(f"  branch_choices={results['search']['branch_choices']}")
    print(f"  best_assigned={results['search']['best_assigned']}")
    print(f"  timed_out={results['search']['timed_out']}")
    print(f"  sampling_attempts={results['search']['sampling_attempts']}")
    print(f"  sampling_successes={results['search']['sampling_successes']}")
    print("Counts (all cycles):")
    for key, value in counts_all.items():
        print(f"  {key}={value}")
    print("Counts (no-EC subset):")
    for key, value in counts_no_ec.items():
        print(f"  {key}={value}")
    print(f"SORRY_BRANCH count={len(sorry_branch)}")
    if sorry_branch:
        print("SORRY_BRANCH cycles:")
        for idx, cycle in enumerate(sorry_branch, start=1):
            proc1 = cycle["proc1"]
            print(
                f"  #{idx}: moverWord={cycle['moverWord']} "
                f"disp={proc1['totalDisplacement']} J={proc1['J']} K={proc1['K']}"
            )
    else:
        print("SORRY_BRANCH cycles: none")
    print(f"results_json={RESULTS_PATH}")


if __name__ == "__main__":
    main()
