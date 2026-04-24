#!/usr/bin/env python3
"""Diagnose seeded-cycle completion failures and endpoint contexts."""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from scripts.p2_completion_search import build_initial_domains_from_cycle, iter_configs, tarjan_scc
from scripts.p2_good_cycle_search import local_context
from scripts.p2_seeded_cycle_search import solve_good_cycle_from_movers
from scripts.p2_smt_completion import solve_cycle_with_smt


def parse_int_tuple(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def forced_scc_summary(state_counts: tuple[int, ...], cycle, movers):
    cycle, cycle_set, domains = build_initial_domains_from_cycle(state_counts, cycle, movers)
    configs = iter_configs(state_counts)
    index = {config: idx for idx, config in enumerate(configs)}
    forced_edges = [[] for _ in configs]

    for idx, config in enumerate(configs):
        if config in cycle_set:
            continue
        for processor in range(len(state_counts)):
            key = (processor, local_context(config, processor))
            domain = domains[key]
            if len(domain) != 1:
                continue
            (out_state,) = tuple(domain)
            if out_state == config[processor]:
                continue
            nxt = list(config)
            nxt[processor] = out_state
            forced_edges[idx].append((processor, index[tuple(nxt)]))

    adjacency = [[dst for _, dst in edges if configs[dst] not in cycle_set] for edges in forced_edges]
    required = set(range(len(state_counts)))

    for scc in tarjan_scc(adjacency):
        if len(scc) <= 1:
            continue
        scc_set = set(scc)
        seen = set()
        bad_nodes = []
        for node in scc:
            internal = [(p, d) for p, d in forced_edges[node] if d in scc_set]
            if len(forced_edges[node]) != 1 or len(internal) != 1:
                bad_nodes.append((configs[node], forced_edges[node], internal))
            else:
                seen.add(internal[0][0])
        if bad_nodes or seen != required:
            ones_hist = Counter(sum(configs[node]) for node in scc)
            defect_hist = Counter(
                sum(1 for i in range(len(state_counts)) if configs[node][i] != configs[node][(i + 1) % len(state_counts)])
                for node in scc
            )
            outdegree_hist = Counter(len(forced_edges[node]) for node in scc)
            internal_mover_hist = Counter()
            for node in scc:
                for processor, dst in forced_edges[node]:
                    if dst in scc_set:
                        internal_mover_hist[processor] += 1
            return {
                "scc_size": len(scc),
                "all_binary": all(all(value in (0, 1) for value in configs[node]) for node in scc),
                "ones_hist": dict(sorted(ones_hist.items())),
                "ring_defect_hist": dict(sorted(defect_hist.items())),
                "forced_outdegree_hist": dict(sorted(outdegree_hist.items())),
                "internal_mover_hist": dict(sorted(internal_mover_hist.items())),
                "sample_bad_nodes": [
                    (
                        cfg,
                        [(p, configs[d]) for p, d in edges],
                        [(p, configs[d]) for p, d in internal],
                    )
                    for cfg, edges, internal in bad_nodes[:8]
                ],
            }
    return None


def print_endpoint_contexts(cycle, movers) -> None:
    n = len(cycle[0])
    for step, (cfg, mover) in enumerate(zip(cycle, movers, strict=True)):
        if mover not in {0, n - 1}:
            continue
        ctx0 = local_context(cfg, 0)
        out0 = cycle[(step + 1) % len(cycle)][0] if mover == 0 else cfg[0]
        ctxn = local_context(cfg, n - 1)
        outn = cycle[(step + 1) % len(cycle)][n - 1] if mover == n - 1 else cfg[n - 1]
        print(f"step={step} mover={mover} cfg={cfg}")
        print(f"  P0   ctx={ctx0} out={out0}")
        print(f"  P{n-1} ctx={ctxn} out={outn}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--state-counts", default="2,3,3,3,3,3,3,3,2")
    parser.add_argument("--movers", required=True)
    parser.add_argument("--cycle-timeout-ms", type=int, default=5000)
    parser.add_argument("--completion-timeout-ms", type=int, default=30000)
    args = parser.parse_args()

    state_counts = parse_int_tuple(args.state_counts)
    movers = parse_int_tuple(args.movers)

    cycle_result = solve_good_cycle_from_movers(state_counts, movers, timeout_ms=args.cycle_timeout_ms)
    print(f"cycle_found={cycle_result.found} message={cycle_result.message} elapsed={cycle_result.elapsed:.3f}s")
    if cycle_result.cycle is None:
        return

    print_endpoint_contexts(cycle_result.cycle, movers)
    completion = solve_cycle_with_smt(
        state_counts,
        cycle_result.cycle,
        movers,
        timeout_ms=args.completion_timeout_ms,
    )
    print(f"completion_found={completion.found} message={completion.message} elapsed={completion.elapsed:.3f}s")
    if completion.found:
        return

    summary = forced_scc_summary(state_counts, cycle_result.cycle, movers)
    if summary is None:
        print("no fatal forced SCC found in initial propagation snapshot")
        return

    for key, value in summary.items():
        print(f"{key}={value}")


if __name__ == "__main__":
    main()
