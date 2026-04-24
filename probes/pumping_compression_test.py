#!/usr/bin/env python3
"""Test whether CUP-2 bad cycles admit a pumping/compression argument.

This script follows the exact local Lean/Dijkstra notion of bad step:

  badStep gc c' c  :=  c ∉ gc.configs ∧ c' ∉ gc.configs ∧ step c c'

So all cycle searches here are relative to the explicit good cycle only,
not the larger tail basin used by `verify_system`.

Tasks covered:
1. Enumerate all off-good-cycle bad cycles for CUP-2 at n=9,10,11.
2. Test whether deleting a uniform interior site k ∈ {4,5} preserves cycles.
3. Repeat for TP-preserving bad cycles, where TP is the local repository
   invariant (Exp2Count, Int21Count, Exp2Weight).
4. Report maximum bad-cycle lengths and simple column-duplication diagnostics
   on uniform interior positions 3..n-4 (0-based).

Important caveat:
- If the bad-step graph is already a DAG, then the cycle census is empty and
  every compression question is vacuous. The script reports that explicitly.
"""

from __future__ import annotations

import argparse
import os
import sys
import time
from collections import Counter
from dataclasses import dataclass
from itertools import product
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

ROOT = os.path.dirname(__file__)
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from seam_counterexample_analysis import (  # noqa: E402
    Config,
    delete_config,
    format_cfg,
    good_cycle_configs,
    move,
    tp_invariant,
)


Cycle = Tuple[int, ...]


def cup2_m(n: int, i: int) -> int:
    return 2 if i == 0 or i == n - 1 else 3


def uniform_positions(n: int) -> List[int]:
    """Uniform bulk positions 3..n-4, inclusive, in 0-based indexing."""
    return list(range(3, n - 3))


def all_configs(n: int) -> List[Config]:
    return list(product(*(range(cup2_m(n, i)) for i in range(n))))


def kosaraju_scc(
    succ: Sequence[Sequence[int]],
    rev: Sequence[Sequence[int]],
) -> Tuple[List[int], List[List[int]]]:
    node_count = len(succ)
    seen = [False] * node_count
    order: List[int] = []

    for start in range(node_count):
        if seen[start]:
            continue
        stack: List[Tuple[int, int]] = [(start, 0)]
        seen[start] = True
        while stack:
            node, idx = stack[-1]
            if idx < len(succ[node]):
                nxt = succ[node][idx]
                stack[-1] = (node, idx + 1)
                if not seen[nxt]:
                    seen[nxt] = True
                    stack.append((nxt, 0))
            else:
                order.append(node)
                stack.pop()

    comp_of = [-1] * node_count
    comp_nodes: List[List[int]] = []
    for start in reversed(order):
        if comp_of[start] != -1:
            continue
        cid = len(comp_nodes)
        comp_nodes.append([])
        stack = [start]
        comp_of[start] = cid
        while stack:
            node = stack.pop()
            comp_nodes[cid].append(node)
            for prv in rev[node]:
                if comp_of[prv] == -1:
                    comp_of[prv] = cid
                    stack.append(prv)

    return comp_of, comp_nodes


def enumerate_simple_cycles_in_scc(
    scc_nodes: Sequence[int],
    succ: Sequence[Sequence[int]],
) -> List[Cycle]:
    """Enumerate all simple directed cycles in one SCC.

    This is a start-minimal DFS:
    - every cycle is enumerated exactly once from its minimum node id
    - good enough here because the SCC census in the target runs is empty
    """

    node_set = set(scc_nodes)
    starts = sorted(scc_nodes)
    cycles: List[Cycle] = []

    for start in starts:
        path = [start]
        on_path = {start}

        def dfs(node: int) -> None:
            for nxt in succ[node]:
                if nxt not in node_set or nxt < start:
                    continue
                if nxt == start:
                    cycles.append(tuple(path))
                    continue
                if nxt in on_path:
                    continue
                on_path.add(nxt)
                path.append(nxt)
                dfs(nxt)
                path.pop()
                on_path.remove(nxt)

        dfs(start)

    return cycles


@dataclass(frozen=True)
class GraphSummary:
    n: int
    tp_only: bool
    bad_nodes: int
    bad_edges: int
    scc_count: int
    nontrivial_scc_count: int
    largest_scc_sizes: Tuple[int, ...]
    cycle_count: int
    max_cycle_length: int


@dataclass(frozen=True)
class CompressionSummary:
    k: int
    total_cycles: int
    strict_successes: int
    walk_successes: int
    failure_reasons: Dict[str, int]
    sample_failure_cycle_len: Optional[int]
    sample_failure_reasons: Tuple[str, ...]


@dataclass(frozen=True)
class ColumnSummary:
    total_cycles: int
    adjacent_identical_cycles: int
    any_repeated_cycles: int
    sample_adjacent_pairs: Tuple[Tuple[int, int], ...]


class BadGraph:
    def __init__(self, n: int, tp_only: bool):
        self.n = n
        self.tp_only = tp_only
        self.good_cycle = good_cycle_configs(n)
        self.all_configs = all_configs(n)
        self.bad_configs = [cfg for cfg in self.all_configs if cfg not in self.good_cycle]
        self.bad_id = {cfg: idx for idx, cfg in enumerate(self.bad_configs)}

        tp_cache: Optional[Dict[Config, Tuple[int, int, int]]] = None
        if tp_only:
            tp_cache = {cfg: tp_invariant(cfg) for cfg in self.bad_configs}
        self.tp_cache = tp_cache

        self.succ_map: List[Dict[int, int]] = [dict() for _ in self.bad_configs]
        self.rev: List[List[int]] = [[] for _ in self.bad_configs]
        edge_count = 0
        for src_id, cfg in enumerate(self.bad_configs):
            src_tp = tp_cache[cfg] if tp_cache is not None else None
            for mover in range(n):
                dst = move(cfg, mover)
                if dst is None or dst in self.good_cycle:
                    continue
                dst_id = self.bad_id[dst]
                if src_tp is not None and tp_cache[dst] != src_tp:
                    continue
                self.succ_map[src_id][dst_id] = mover
                self.rev[dst_id].append(src_id)
                edge_count += 1
        self.bad_edges = edge_count
        self.succ_lists: List[List[int]] = [list(d.keys()) for d in self.succ_map]

        self.comp_of, self.comp_nodes = kosaraju_scc(self.succ_lists, self.rev)
        self.nontrivial_sccs = [comp for comp in self.comp_nodes if len(comp) > 1]
        self._cycles: Optional[List[Cycle]] = None

    def summarize(self) -> GraphSummary:
        cycles = self.cycles()
        largest = tuple(sorted((len(scc) for scc in self.nontrivial_sccs), reverse=True)[:10])
        max_cycle_length = max((len(cyc) for cyc in cycles), default=0)
        return GraphSummary(
            n=self.n,
            tp_only=self.tp_only,
            bad_nodes=len(self.bad_configs),
            bad_edges=self.bad_edges,
            scc_count=len(self.comp_nodes),
            nontrivial_scc_count=len(self.nontrivial_sccs),
            largest_scc_sizes=largest,
            cycle_count=len(cycles),
            max_cycle_length=max_cycle_length,
        )

    def cycles(self) -> List[Cycle]:
        if self._cycles is not None:
            return self._cycles
        if not self.nontrivial_sccs:
            self._cycles = []
            return self._cycles

        out: List[Cycle] = []
        for scc in self.nontrivial_sccs:
            out.extend(enumerate_simple_cycles_in_scc(scc, self.succ_lists))
        self._cycles = out
        return out

    def edge_mover(self, src_id: int, dst_id: int) -> int:
        return self.succ_map[src_id][dst_id]

    def edge_exists(self, src: Config, dst: Config) -> bool:
        src_id = self.bad_id.get(src)
        dst_id = self.bad_id.get(dst)
        if src_id is None or dst_id is None:
            return False
        return dst_id in self.succ_map[src_id]


def cycle_configs(graph: BadGraph, cycle: Cycle) -> List[Config]:
    return [graph.bad_configs[node] for node in cycle]


def cycle_movers(graph: BadGraph, cycle: Cycle) -> List[int]:
    if not cycle:
        return []
    out = []
    clen = len(cycle)
    for i, src in enumerate(cycle):
        dst = cycle[(i + 1) % clen]
        out.append(graph.edge_mover(src, dst))
    return out


def analyze_compression(
    graph: BadGraph,
    cycles: Sequence[Cycle],
    k: int,
    small_graph: BadGraph,
) -> CompressionSummary:
    strict_successes = 0
    walk_successes = 0
    failure_reasons = Counter()
    sample_failure_cycle_len: Optional[int] = None
    sample_failure_reasons: Tuple[str, ...] = ()

    for cyc in cycles:
        configs = cycle_configs(graph, cyc)
        movers = cycle_movers(graph, cyc)
        projected = [delete_config(cfg, k) for cfg in configs]
        reasons = set()

        walk_ok = True
        clen = len(configs)
        for i in range(clen):
            src_big = configs[i]
            dst_big = configs[(i + 1) % clen]
            src_small = projected[i]
            dst_small = projected[(i + 1) % clen]
            mover = movers[i]

            if mover == k:
                reasons.add("mover_at_deleted_site")
            if src_small == dst_small:
                reasons.add("projected_step_collapsed")
            if src_small in small_graph.good_cycle or dst_small in small_graph.good_cycle:
                reasons.add("projects_into_good_cycle")
            if not small_graph.edge_exists(src_small, dst_small):
                reasons.add("projected_pair_not_bad_step")
                walk_ok = False

            # Keep the original big-step closure bug visible in the failure mix.
            if src_big == dst_big:
                reasons.add("original_step_collapsed")

        if walk_ok:
            walk_successes += 1
            if len(set(projected)) == len(projected):
                strict_successes += 1
            else:
                reasons.add("projects_to_closed_walk_with_duplicates")

        if reasons:
            failure_reasons.update(reasons)
            if sample_failure_cycle_len is None:
                sample_failure_cycle_len = len(cyc)
                sample_failure_reasons = tuple(sorted(reasons))

    return CompressionSummary(
        k=k,
        total_cycles=len(cycles),
        strict_successes=strict_successes,
        walk_successes=walk_successes,
        failure_reasons=dict(sorted(failure_reasons.items())),
        sample_failure_cycle_len=sample_failure_cycle_len,
        sample_failure_reasons=sample_failure_reasons,
    )


def column_signature(configs: Sequence[Config], pos: int) -> Tuple[Tuple[int, int, int], ...]:
    return tuple((cfg[pos - 1], cfg[pos], cfg[pos + 1]) for cfg in configs)


def analyze_columns(graph: BadGraph, cycles: Sequence[Cycle]) -> ColumnSummary:
    adj_cycles = 0
    repeated_cycles = 0
    sample_pairs: List[Tuple[int, int]] = []
    positions = uniform_positions(graph.n)

    for cyc in cycles:
        configs = cycle_configs(graph, cyc)
        cols = {pos: column_signature(configs, pos) for pos in positions}

        repeated_any = len(set(cols.values())) < len(cols)
        if repeated_any:
            repeated_cycles += 1

        pairs = [(pos, pos + 1) for pos in positions[:-1] if cols[pos] == cols[pos + 1]]
        if pairs:
            adj_cycles += 1
            if not sample_pairs:
                sample_pairs = pairs

    return ColumnSummary(
        total_cycles=len(cycles),
        adjacent_identical_cycles=adj_cycles,
        any_repeated_cycles=repeated_cycles,
        sample_adjacent_pairs=tuple(sample_pairs),
    )


def format_fraction(num: int, den: int) -> str:
    if den == 0:
        return "N/A"
    return f"{num}/{den} = {num / den:.3f}"


def print_graph_report(label: str, summary: GraphSummary) -> None:
    print(f"{label}:")
    print(
        f"  bad_nodes={summary.bad_nodes} bad_edges={summary.bad_edges} "
        f"sccs={summary.scc_count} nontrivial_sccs={summary.nontrivial_scc_count}"
    )
    if summary.largest_scc_sizes:
        print(f"  largest_scc_sizes={list(summary.largest_scc_sizes)}")
    print(
        f"  cycle_count={summary.cycle_count} "
        f"max_cycle_length={summary.max_cycle_length}"
    )


def print_compression_report(
    label: str,
    graph_summary: GraphSummary,
    compressions: Sequence[CompressionSummary],
) -> None:
    print(label + ":")
    if graph_summary.cycle_count == 0:
        print("  no cycles to compress")
        return
    for comp in compressions:
        print(f"  k={comp.k}:")
        print(f"    strict_cycle_success={format_fraction(comp.strict_successes, comp.total_cycles)}")
        print(f"    closed_walk_success={format_fraction(comp.walk_successes, comp.total_cycles)}")
        if comp.failure_reasons:
            print(f"    failure_reasons={comp.failure_reasons}")
        if comp.sample_failure_reasons:
            print(
                "    sample_failure="
                f"len{comp.sample_failure_cycle_len}:{list(comp.sample_failure_reasons)}"
            )


def print_column_report(label: str, summary: ColumnSummary) -> None:
    print(label + ":")
    if summary.total_cycles == 0:
        print("  no cycles, so the column question is vacuous")
        print("  note: plain pigeonhole can force repeated columns, not adjacent repetition")
        return
    print(
        f"  adjacent_identical={summary.adjacent_identical_cycles}/{summary.total_cycles}"
    )
    print(
        f"  any_repeated={summary.any_repeated_cycles}/{summary.total_cycles}"
    )
    if summary.sample_adjacent_pairs:
        print(f"  sample_adjacent_pairs={list(summary.sample_adjacent_pairs)}")


def analyze_n(n: int, ks: Sequence[int]) -> None:
    print("=" * 88)
    print(f"n={n}")

    full_graph = BadGraph(n, tp_only=False)
    full_summary = full_graph.summarize()
    full_cycles = full_graph.cycles()
    print_graph_report("All bad-step graph", full_summary)

    full_compressions: List[CompressionSummary] = []
    if full_cycles:
        for k in ks:
            if not (0 <= k < n):
                continue
            small_graph = BadGraph(n - 1, tp_only=False)
            full_compressions.append(analyze_compression(full_graph, full_cycles, k, small_graph))
    print_compression_report("Compression on all bad cycles", full_summary, full_compressions)
    print_column_report("Columns on all bad cycles", analyze_columns(full_graph, full_cycles))

    tp_graph = BadGraph(n, tp_only=True)
    tp_summary = tp_graph.summarize()
    tp_cycles = tp_graph.cycles()
    print_graph_report("TP-preserving bad-step graph", tp_summary)

    tp_compressions: List[CompressionSummary] = []
    if tp_cycles:
        for k in ks:
            if not (0 <= k < n):
                continue
            small_tp_graph = BadGraph(n - 1, tp_only=True)
            tp_compressions.append(analyze_compression(tp_graph, tp_cycles, k, small_tp_graph))
    print_compression_report("Compression on TP-preserving bad cycles", tp_summary, tp_compressions)
    print_column_report("Columns on TP-preserving bad cycles", analyze_columns(tp_graph, tp_cycles))

    print("Bottom line:")
    if full_summary.cycle_count == 0:
        print("  exact off-good-cycle bad-step graph is already a DAG")
    else:
        print("  off-good-cycle bad cycles exist")
    if tp_summary.cycle_count == 0:
        print("  TP-preserving bad-step graph is also a DAG")
    else:
        print("  TP-preserving bad cycles exist")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--ns",
        type=int,
        nargs="+",
        default=[9, 10, 11],
        help="ring sizes to analyze",
    )
    parser.add_argument(
        "--ks",
        type=int,
        nargs="+",
        default=[4, 5],
        help="delete sites to test",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    t0 = time.time()
    print("CUP-2 pumping/compression test")
    print("badStep semantics: off the explicit good cycle only")
    print(f"ring sizes={args.ns} delete_sites={args.ks}")
    for n in args.ns:
        analyze_n(n, args.ks)
    elapsed = time.time() - t0
    print("=" * 88)
    print(f"done in {elapsed:.3f}s")
    print("Pigeonhole note:")
    print("  If a bad cycle had length L, a uniform interior column has at most 27^L possibilities.")
    print("  That can force some repeated column when n-6 > 27^L, but not adjacent equality by itself.")


if __name__ == "__main__":
    main()
