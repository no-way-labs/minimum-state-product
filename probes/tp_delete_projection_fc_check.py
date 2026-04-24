#!/usr/bin/env python3
"""Check deletion projection/containment and fc monotonicity for TP-reachability.

For fixed ``n`` and deletion site ``k``:

  S_n(c) := TP-bad-reachable set from ``c`` at size ``n``

This script checks two stronger hypotheses behind
``PhiFull(delete(c)) <= PhiFull(c)``:

1. Projection through deletion:
     delete(S_n(c)) ⊆ S_{n-1}(delete(c))
   and
     S_{n-1}(delete(c)) ⊆ delete(S_n(c))

2. Frontier-count monotonicity under deletion:
     fc(delete(d)) <= fc(d)

The TP graph semantics are imported from ``seam_counterexample_analysis.py``,
which already matches the local Lean/CUP-2 model used for ``source_transport``.
"""

from __future__ import annotations

import argparse
import time
from collections import Counter, deque
from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

try:
    from seam_counterexample_analysis import TpGraph, delete_config, format_cfg
except ModuleNotFoundError:
    from probes.seam_counterexample_analysis import (
        TpGraph,
        delete_config,
        format_cfg,
    )


Config = Tuple[int, ...]


def topo_order(succ: List[List[int]], rev: List[List[int]]) -> List[int]:
    indeg = [len(preds) for preds in rev]
    queue = deque(i for i, deg in enumerate(indeg) if deg == 0)
    order: List[int] = []
    while queue:
        cid = queue.popleft()
        order.append(cid)
        for nxt in succ[cid]:
            indeg[nxt] -= 1
            if indeg[nxt] == 0:
                queue.append(nxt)
    if len(order) != len(succ):
        raise RuntimeError("condensation graph must be acyclic")
    return order


def build_comp_reachable_state_masks(
    graph: TpGraph,
) -> Tuple[Dict[Config, int], List[int]]:
    graph.ensure_scc()
    cfg_index = {cfg: idx for idx, cfg in enumerate(graph.all_configs)}
    direct_masks = [0] * len(graph.comp_nodes)
    for cid, nodes in enumerate(graph.comp_nodes):
        mask = 0
        for node in nodes:
            mask |= 1 << cfg_index[graph.bad_configs[node]]
        direct_masks[cid] = mask

    order = topo_order(graph.comp_succ, graph.comp_rev)
    reach_masks = direct_masks[:]
    for cid in reversed(order):
        mask = reach_masks[cid]
        for nxt in graph.comp_succ[cid]:
            mask |= reach_masks[nxt]
        reach_masks[cid] = mask
    return cfg_index, reach_masks


def build_comp_reachable_delete_masks(
    big: TpGraph,
    small_index: Dict[Config, int],
    k: int,
) -> List[int]:
    big.ensure_scc()
    direct_masks = [0] * len(big.comp_nodes)
    for cid, nodes in enumerate(big.comp_nodes):
        mask = 0
        for node in nodes:
            deleted = delete_config(big.bad_configs[node], k)
            mask |= 1 << small_index[deleted]
        direct_masks[cid] = mask

    order = topo_order(big.comp_succ, big.comp_rev)
    reach_masks = direct_masks[:]
    for cid in reversed(order):
        mask = reach_masks[cid]
        for nxt in big.comp_succ[cid]:
            mask |= reach_masks[nxt]
        reach_masks[cid] = mask
    return reach_masks


def reachable_state_mask(
    graph: TpGraph,
    cfg_index: Dict[Config, int],
    comp_masks: List[int],
    source: Config,
) -> int:
    if source in graph.good_cycle:
        return 1 << cfg_index[source]
    return comp_masks[graph.comp_of[graph.bad_id[source]]]


def reachable_delete_mask(
    big: TpGraph,
    small_index: Dict[Config, int],
    comp_masks: List[int],
    source: Config,
    k: int,
) -> int:
    if source in big.good_cycle:
        return 1 << small_index[delete_config(source, k)]
    return comp_masks[big.comp_of[big.bad_id[source]]]


def sample_configs_from_mask(
    mask: int,
    configs: Sequence[Config],
    limit: int,
) -> List[Config]:
    out: List[Config] = []
    idx = 0
    cur = mask
    while cur and len(out) < limit:
        if cur & 1:
            out.append(configs[idx])
        cur >>= 1
        idx += 1
    return out


@dataclass(frozen=True)
class ProjectionSample:
    source: Config
    deleted_source: Config
    big_delete_count: int
    small_reach_count: int
    discrepancy_count: int
    discrepancy_samples: Tuple[Config, ...]


@dataclass(frozen=True)
class AnalysisResult:
    n: int
    k: int
    total_sources: int
    total_big_configs: int
    forward_ok: int
    reverse_ok: int
    equality_ok: int
    forward_only: int
    reverse_only: int
    neither: int
    fc_monotone_ok: int
    fc_monotone_violations: int
    fc_delta_hist: Dict[int, int]
    phi_violations: int
    forward_sample: Optional[ProjectionSample]
    reverse_sample: Optional[ProjectionSample]
    fc_sample: Optional[Tuple[Config, Config, int, int]]
    phi_sample: Optional[Tuple[Config, int, int]]


def analyze(n: int, k: int, sample_limit: int) -> AnalysisResult:
    t0 = time.time()
    big = TpGraph(n)
    small = TpGraph(n - 1)
    big.ensure_scc()
    small.ensure_scc()

    small_index, small_reach_masks = build_comp_reachable_state_masks(small)
    big_delete_masks = build_comp_reachable_delete_masks(big, small_index, k)

    total_sources = len(big.all_configs)
    forward_ok = 0
    reverse_ok = 0
    equality_ok = 0
    forward_only = 0
    reverse_only = 0
    neither = 0
    forward_sample: Optional[ProjectionSample] = None
    reverse_sample: Optional[ProjectionSample] = None

    fc_delta_hist = Counter()
    fc_sample: Optional[Tuple[Config, Config, int, int]] = None
    fc_violations = 0
    for cfg in big.all_configs:
        deleted = delete_config(cfg, k)
        fc_big = big.fc_all[cfg]
        fc_small = small.fc_all[deleted]
        delta = fc_small - fc_big
        fc_delta_hist[delta] += 1
        if delta > 0:
            fc_violations += 1
            if fc_sample is None:
                fc_sample = (cfg, deleted, fc_big, fc_small)

    phi_violations = 0
    phi_sample: Optional[Tuple[Config, int, int]] = None

    for cfg in big.all_configs:
        deleted_source = delete_config(cfg, k)
        delete_mask = reachable_delete_mask(big, small_index, big_delete_masks, cfg, k)
        small_mask = reachable_state_mask(small, small_index, small_reach_masks, deleted_source)

        extra = delete_mask & ~small_mask
        missing = small_mask & ~delete_mask
        has_forward = extra == 0
        has_reverse = missing == 0

        if has_forward:
            forward_ok += 1
        if has_reverse:
            reverse_ok += 1
        if has_forward and has_reverse:
            equality_ok += 1
        elif has_forward:
            forward_only += 1
        elif has_reverse:
            reverse_only += 1
        else:
            neither += 1

        if not has_forward and forward_sample is None:
            forward_sample = ProjectionSample(
                source=cfg,
                deleted_source=deleted_source,
                big_delete_count=delete_mask.bit_count(),
                small_reach_count=small_mask.bit_count(),
                discrepancy_count=extra.bit_count(),
                discrepancy_samples=tuple(
                    sample_configs_from_mask(extra, small.all_configs, sample_limit)
                ),
            )

        if not has_reverse and reverse_sample is None:
            reverse_sample = ProjectionSample(
                source=cfg,
                deleted_source=deleted_source,
                big_delete_count=delete_mask.bit_count(),
                small_reach_count=small_mask.bit_count(),
                discrepancy_count=missing.bit_count(),
                discrepancy_samples=tuple(
                    sample_configs_from_mask(missing, small.all_configs, sample_limit)
                ),
            )

        phi_big = big.phi_of(cfg)
        phi_small = small.phi_of(deleted_source)
        if phi_small > phi_big:
            phi_violations += 1
            if phi_sample is None:
                phi_sample = (cfg, phi_small, phi_big)

    elapsed = time.time() - t0
    print(
        f"[n={n} k={k}] built/analyzed in {elapsed:.2f}s | "
        f"big={len(big.all_configs)} configs, small={len(small.all_configs)} configs"
    )

    return AnalysisResult(
        n=n,
        k=k,
        total_sources=total_sources,
        total_big_configs=len(big.all_configs),
        forward_ok=forward_ok,
        reverse_ok=reverse_ok,
        equality_ok=equality_ok,
        forward_only=forward_only,
        reverse_only=reverse_only,
        neither=neither,
        fc_monotone_ok=total_sources - fc_violations,
        fc_monotone_violations=fc_violations,
        fc_delta_hist=dict(sorted(fc_delta_hist.items())),
        phi_violations=phi_violations,
        forward_sample=forward_sample,
        reverse_sample=reverse_sample,
        fc_sample=fc_sample,
        phi_sample=phi_sample,
    )


def print_sample(label: str, sample: Optional[ProjectionSample]) -> None:
    if sample is None:
        print(f"{label}: none")
        return
    print(f"{label}:")
    print(f"  source c = {format_cfg(sample.source)}")
    print(f"  delete(c) = {format_cfg(sample.deleted_source)}")
    print(f"  |delete(S_n(c))| = {sample.big_delete_count}")
    print(f"  |S_(n-1)(delete(c))| = {sample.small_reach_count}")
    print(f"  discrepancy count = {sample.discrepancy_count}")
    if sample.discrepancy_samples:
        print("  sample discrepancy states:")
        for cfg in sample.discrepancy_samples:
            print(f"    {format_cfg(cfg)}")


def print_result(result: AnalysisResult) -> None:
    print(f"=== n={result.n}, k={result.k} ===")
    print(f"total sources c checked: {result.total_sources}")
    print()
    print("Hypothesis B: TP-reachable set projects through deletion")
    print(
        "  forward  delete(S_n(c)) ⊆ S_(n-1)(delete(c)): "
        f"{result.forward_ok}/{result.total_sources}"
    )
    print(
        "  reverse  delete(S_n(c)) ⊇ S_(n-1)(delete(c)): "
        f"{result.reverse_ok}/{result.total_sources}"
    )
    print(
        "  equality delete(S_n(c)) = S_(n-1)(delete(c)): "
        f"{result.equality_ok}/{result.total_sources}"
    )
    print(
        "  breakdown: "
        f"forward_only={result.forward_only}, "
        f"reverse_only={result.reverse_only}, "
        f"neither={result.neither}"
    )
    print_sample("  sample forward failure", result.forward_sample)
    print_sample("  sample reverse failure", result.reverse_sample)
    print()
    print("Hypothesis A: fc(delete(d)) <= fc(d)")
    print(
        "  all big configs d checked: "
        f"{result.total_big_configs}; "
        f"violations={result.fc_monotone_violations}"
    )
    print(f"  Δfc histogram (fc(delete(d)) - fc(d)): {result.fc_delta_hist}")
    if result.fc_sample is not None:
        cfg, deleted, fc_big, fc_small = result.fc_sample
        print(
            "  sample violation: "
            f"d={format_cfg(cfg)} -> delete(d)={format_cfg(deleted)} "
            f"with fc {fc_big} -> {fc_small}"
        )
    print()
    print("Direct PhiFull check")
    print(
        "  configs with PhiFull(delete(c)) > PhiFull(c): "
        f"{result.phi_violations}/{result.total_sources}"
    )
    if result.phi_sample is not None:
        cfg, phi_small, phi_big = result.phi_sample
        print(
            "  sample PhiFull violation: "
            f"c={format_cfg(cfg)} with PhiFull(delete(c))={phi_small}, PhiFull(c)={phi_big}"
        )
    print()


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=9)
    parser.add_argument("--ks", nargs="+", type=int, default=[4, 5])
    parser.add_argument("--sample-limit", type=int, default=5)
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)
    for k in args.ks:
        print_result(analyze(args.n, k, args.sample_limit))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
