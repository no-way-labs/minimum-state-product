#!/usr/bin/env python3
"""Exhaustive shadow-trap test for consecutive binary processors.

Task:
- n = 4
- ms = (2, 2, 2, 3)
- Enumerate all directed Hamiltonian good cycles through the full 24-config graph
- For each cycle, flip processors 0 and 2 in every cycle config
- At each shadow config, check whether some processor is forced privileged by the
  local rule entries determined by the good cycle
"""

from __future__ import annotations

import json
import time
from collections import Counter
from dataclasses import dataclass
from itertools import product


MS = (2, 2, 2, 3)
N = 4
START_CONFIG = (0, 0, 0, 0)
RESULTS_PATH = "ra_shadow_consec_results.json"


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

        self.stats = {
            "nodes": 0,
            "forced_assignments": 0,
            "branch_choices": 0,
            "best_assigned": 0,
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

    def enumerate_exhaustive(self) -> list[tuple[list[tuple[int, ...]], list[int]]]:
        initial_rules = tuple([-1] * len(self.rule_keys))
        initial_incoming = tuple([-1] * self.total)
        initial_outgoing = tuple([-1] * self.total)
        found: list[tuple[list[tuple[int, ...]], list[int]]] = []

        def dfs(
            rules: tuple[int, ...],
            incoming: tuple[int, ...],
            outgoing: tuple[int, ...],
        ) -> None:
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
                    found.append(self.extract_cycle(outgoing_p))
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

            candidates = [
                edge_idx
                for edge_idx in range(len(self.edges[branch_src]))
                if branch_mask & (1 << edge_idx)
            ]
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


def build_forced_table(
    configs: list[tuple[int, ...]],
    movers: list[int],
    ms: tuple[int, ...],
) -> dict[tuple[int, int, int, int], int]:
    table: dict[tuple[int, int, int, int], int] = {}
    n = len(ms)
    cycle_len = len(configs)
    for step in range(cycle_len):
        config = configs[step]
        next_config = configs[(step + 1) % cycle_len]
        mover = movers[step]
        for proc in range(n):
            key = (proc, *local_context(config, proc, n))
            out = next_config[proc] if proc == mover else config[proc]
            prev = table.get(key)
            if prev is not None and prev != out:
                raise ValueError(f"inconsistent forced table at {key}: {prev} vs {out}")
            table[key] = out
    return table


def flip_0_2(config: tuple[int, ...]) -> tuple[int, ...]:
    return (1 - config[0], config[1], 1 - config[2], config[3])


def forced_privileged_set(
    config: tuple[int, ...],
    forced_table: dict[tuple[int, int, int, int], int],
    n: int,
) -> list[int]:
    privileged: list[int] = []
    for proc in range(n):
        key = (proc, *local_context(config, proc, n))
        out = forced_table.get(key)
        if out is not None and out != config[proc]:
            privileged.append(proc)
    return privileged


def shadow_analysis(
    configs: list[tuple[int, ...]],
    movers: list[int],
    ms: tuple[int, ...],
) -> dict:
    forced_table = build_forced_table(configs, movers, ms)
    good_set = set(configs)
    step_records = []
    failure_steps = []
    privilege_count_hist = Counter()

    for step, config in enumerate(configs):
        shadow = flip_0_2(config)
        privs = forced_privileged_set(shadow, forced_table, len(ms))
        privilege_count_hist[len(privs)] += 1
        record = {
            "step": step,
            "goodConfig": list(config),
            "shadowConfig": list(shadow),
            "forcedPrivileged": privs,
            "hitsGoodCycle": shadow in good_set,
        }
        step_records.append(record)
        if not privs:
            failure_steps.append(record)

    return {
        "works": not failure_steps,
        "stepCount": len(configs),
        "stepsWithForcedPrivilege": len(configs) - len(failure_steps),
        "failingStepCount": len(failure_steps),
        "failingSteps": failure_steps,
        "privilegeCountHistogram": {str(k): v for k, v in sorted(privilege_count_hist.items())},
        "shadowHitsGoodCycleCount": sum(1 for record in step_records if record["hitsGoodCycle"]),
        "shadowStepRecords": step_records,
    }


def cycle_summary(index: int, configs: list[tuple[int, ...]], movers: list[int], ms: tuple[int, ...]) -> dict:
    shadow = shadow_analysis(configs, movers, ms)
    fire_counts = Counter(movers)
    return {
        "index": index,
        "length": len(configs),
        "startConfig": list(configs[0]),
        "moverWord": movers,
        "fireCounts": {str(proc): fire_counts.get(proc, 0) for proc in range(len(ms))},
        "configs": [list(cfg) for cfg in configs],
        "shadow": shadow,
    }


def main() -> None:
    started = time.monotonic()
    enumerator = HamiltonianCycleEnumerator(MS)
    cycles = enumerator.enumerate_exhaustive()
    elapsed = time.monotonic() - started

    summaries = [
        cycle_summary(idx, configs, movers, MS)
        for idx, (configs, movers) in enumerate(cycles, start=1)
    ]

    successes = [summary for summary in summaries if summary["shadow"]["works"]]
    failures = [summary for summary in summaries if not summary["shadow"]["works"]]

    results = {
        "n": N,
        "ms": list(MS),
        "graph": {
            "configCount": enumerator.total,
            "directedEdgeCount": sum(len(src_edges) for src_edges in enumerator.edges),
            "perConfigDegree": len(enumerator.edges[0]),
            "ruleKeyCount": len(enumerator.rule_keys),
        },
        "search": {
            **enumerator.stats,
            "elapsedSec": elapsed,
        },
        "counts": {
            "hamiltonianGoodCycles": len(summaries),
            "shadowSuccesses": len(successes),
            "shadowFailures": len(failures),
        },
        "cycleSummaries": summaries,
    }

    with open(RESULTS_PATH, "w", encoding="utf-8") as fh:
        json.dump(results, fh, indent=2)

    print(f"n={N}, ms={MS}")
    print(f"configs={results['graph']['configCount']}")
    print(f"directed_edges={results['graph']['directedEdgeCount']}")
    print(f"per_config_degree={results['graph']['perConfigDegree']}")
    print(f"rule_keys={results['graph']['ruleKeyCount']}")
    print("search_stats:")
    print(f"  elapsed_sec={results['search']['elapsedSec']:.6f}")
    print(f"  nodes={results['search']['nodes']}")
    print(f"  forced_assignments={results['search']['forced_assignments']}")
    print(f"  branch_choices={results['search']['branch_choices']}")
    print(f"  best_assigned={results['search']['best_assigned']}")
    print("counts:")
    print(f"  hamiltonian_good_cycles={results['counts']['hamiltonianGoodCycles']}")
    print(f"  shadow_successes={results['counts']['shadowSuccesses']}")
    print(f"  shadow_failures={results['counts']['shadowFailures']}")

    if summaries:
        print("cycle_results:")
        for summary in summaries:
            shadow = summary["shadow"]
            print(
                f"  cycle#{summary['index']}: "
                f"shadow_works={shadow['works']} "
                f"failing_steps={shadow['failingStepCount']} "
                f"shadow_hits_good={shadow['shadowHitsGoodCycleCount']} "
                f"movers={summary['moverWord']}"
            )
            if not shadow["works"]:
                print(f"    failure_steps={[item['step'] for item in shadow['failingSteps']]}")
    else:
        print("note:")
        print("  No directed Hamiltonian good cycle exists on the 24-config graph for ms=(2,2,2,3).")
        print("  The shadow test is therefore vacuous for this exact setup.")

    print(f"results_json={RESULTS_PATH}")


if __name__ == "__main__":
    main()
