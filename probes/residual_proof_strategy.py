#!/usr/bin/env python3
"""Residual-proof strategy scan for `source_transport_residual_le`.

This script works at the exact Lean semantics used in:
  - `PhiFullTP.lean` for TP-bad reachability and `cup2PhiFull`
  - `CPhiDelete.lean` for deletion at a deep site

For a fixed `(n, k)`, it checks the user-proposed mechanisms:

1. Exact lift versus unlifted states in `S_{n-1}(delete(c))`.
2. Whether every unlifted state is `fc`-bounded by the source `c`.
3. Whether every unlifted state is a single seam step from a lifted state.
4. Whether `delete(S_n(c)) ⊆ S_{n-1}(delete(c))`.
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter, deque
from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple


ROOT = os.path.dirname(__file__)
sys.path.insert(0, ROOT)

from source_transport_seam_research import (  # type: ignore
    Config,
    TpBadGraph,
    delete_config,
    format_cfg,
    valid_sites,
)
from source_transport_global_research import (  # type: ignore
    component_desc_bits,
    reachable_bad_nodes,
)


@dataclass
class ReachCache:
    graph: TpBadGraph
    desc_bits: List[int]
    nodes: Dict[Config, Tuple[Config, ...]]

    def get(self, cfg: Config) -> Tuple[Config, ...]:
        cached = self.nodes.get(cfg)
        if cached is not None:
            return cached
        if cfg in self.graph.good_cycle:
            out = (cfg,)
        else:
            out = tuple(reachable_bad_nodes(self.graph, self.desc_bits, cfg))
        self.nodes[cfg] = out
        return out


@dataclass
class PathResult:
    nodes: List[Config]
    movers: List[int]


@dataclass
class UnliftedSample:
    c: Config
    deleted: Config
    dprime: Config
    fc_c: int
    fc_dprime: int
    defect: int
    path: PathResult
    seam_pred: Optional[Config]
    seam_mover: Optional[int]


@dataclass
class DeleteSubsetFailure:
    c: Config
    deleted_c: Config
    d: Config
    deleted_d: Config
    path: PathResult


def summarize_counter(counter: Counter[int]) -> str:
    if not counter:
        return "(empty)"
    return ", ".join(f"{key}:{counter[key]}" for key in sorted(counter))


def build_rev_with_movers(graph: TpBadGraph) -> List[List[Tuple[int, int]]]:
    rev: List[List[Tuple[int, int]]] = [[] for _ in graph.bad_configs]
    for src_id, edges in enumerate(graph.out_edges):
        for dst_id, mover in edges:
            rev[dst_id].append((src_id, mover))
    return rev


def bfs_path_bad(graph: TpBadGraph, src: Config, target: Config) -> Optional[PathResult]:
    if src == target:
        return PathResult(nodes=[src], movers=[])
    if src in graph.good_cycle or target in graph.good_cycle:
        return None

    src_id = graph.bad_id[src]
    target_id = graph.bad_id[target]
    parent: Dict[int, Tuple[Optional[int], Optional[int]]] = {src_id: (None, None)}
    q = deque([src_id])

    while q:
        node = q.popleft()
        for nxt, mover in graph.out_edges[node]:
            if nxt in parent:
                continue
            parent[nxt] = (node, mover)
            if nxt == target_id:
                q.clear()
                break
            q.append(nxt)

    if target_id not in parent:
        return None

    ids: List[int] = []
    movers: List[int] = []
    cur: Optional[int] = target_id
    while cur is not None:
        ids.append(cur)
        prev, mover = parent[cur]
        if mover is not None:
            movers.append(mover)
        cur = prev
    ids.reverse()
    movers.reverse()
    return PathResult(nodes=[graph.bad_configs[i] for i in ids], movers=movers)


def build_exact_delete_index(nodes: Iterable[Config], k: int) -> Dict[Config, Config]:
    out: Dict[Config, Config] = {}
    for node in nodes:
        deleted = delete_config(node, k)
        out.setdefault(deleted, node)
    return out


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=9)
    parser.add_argument("--k", type=int, default=4)
    parser.add_argument("--samples", type=int, default=4)
    args = parser.parse_args(argv)

    if args.k not in valid_sites(args.n):
        raise SystemExit(f"k must be one of {valid_sites(args.n)} for n={args.n}")

    big = TpBadGraph(args.n)
    small = TpBadGraph(args.n - 1)
    big.ensure_scc()
    small.ensure_scc()

    big_reach = ReachCache(big, component_desc_bits(big), {})
    small_reach = ReachCache(small, component_desc_bits(small), {})
    small_rev = build_rev_with_movers(small)
    seam = {args.k - 1, args.k}

    total_sources = 0
    total_pairs = 0

    lifted_pairs = 0
    unlifted_pairs = 0
    sources_with_unlifted = 0
    unlifted_achiever_pairs = 0
    sources_with_unlifted_achiever = 0
    unlifted_fc_violation = 0
    unlifted_achiever_fc_violation = 0
    max_unlifted_delta = Counter()

    strategy_fail_pairs = 0
    strategy_fail_sources = 0
    achiever_strategy_fail_pairs = 0
    achiever_strategy_fail_sources = 0
    direct_seam_pred_pairs = 0
    direct_seam_pred_achiever_pairs = 0
    seam_gap = Counter()
    seam_gap_gt_one = 0
    seam_gap_gt_defect = 0

    delete_subset_pair_fail = 0
    delete_subset_source_fail = 0

    unlifted_samples: List[UnliftedSample] = []
    strategy_fail_samples: List[UnliftedSample] = []
    delete_subset_failure: Optional[DeleteSubsetFailure] = None

    for c in big.all_configs:
        total_sources += 1
        deleted = delete_config(c, args.k)
        fc_c = big.fc_all[c]
        fc_deleted = small.fc_all[deleted]
        defect = fc_c - fc_deleted
        phi_small = small.phi_of(deleted)

        big_nodes = big_reach.get(c)
        small_nodes = small_reach.get(deleted)
        small_set = set(small_nodes)
        exact_delete = build_exact_delete_index(big_nodes, args.k)
        lifted_set = set(exact_delete)
        unlifted = [dprime for dprime in small_nodes if dprime not in lifted_set]

        total_pairs += len(small_nodes)
        lifted_pairs += len(small_nodes) - len(unlifted)
        unlifted_pairs += len(unlifted)
        if unlifted:
            sources_with_unlifted += 1
            max_unlifted_delta[max(small.fc_all[dprime] - fc_c for dprime in unlifted)] += 1
        else:
            max_unlifted_delta[-999] += 1

        source_has_strategy_fail = False
        source_has_achiever_strategy_fail = False

        if c not in big.good_cycle:
            for d in big_nodes:
                deleted_d = delete_config(d, args.k)
                if deleted_d not in small_set:
                    delete_subset_pair_fail += 1
                    if delete_subset_failure is None:
                        path = bfs_path_bad(big, c, d)
                        if path is None:
                            raise RuntimeError("missing bad path for delete-image failure")
                        delete_subset_failure = DeleteSubsetFailure(c, deleted, d, deleted_d, path)
                    source_has_strategy_fail = source_has_strategy_fail
            if any(delete_config(d, args.k) not in small_set for d in big_nodes):
                delete_subset_source_fail += 1

        for dprime in unlifted:
            fc_dprime = small.fc_all[dprime]
            if fc_dprime > fc_c:
                unlifted_fc_violation += 1

            is_achiever = fc_dprime == phi_small
            if is_achiever:
                unlifted_achiever_pairs += 1
                if fc_dprime > fc_c:
                    unlifted_achiever_fc_violation += 1

            seam_preds: List[Tuple[Config, int]] = []
            if dprime not in small.good_cycle:
                dprime_id = small.bad_id[dprime]
                for pred_id, mover in small_rev[dprime_id]:
                    pred_cfg = small.bad_configs[pred_id]
                    if mover in seam and pred_cfg in lifted_set:
                        seam_preds.append((pred_cfg, mover))

            if seam_preds:
                direct_seam_pred_pairs += 1
                if is_achiever:
                    direct_seam_pred_achiever_pairs += 1
                best_pred, best_mover = max(seam_preds, key=lambda item: (small.fc_all[item[0]], item[0]))
                gap = fc_dprime - small.fc_all[best_pred]
                seam_gap[gap] += 1
                if gap > 1:
                    seam_gap_gt_one += 1
                if gap > defect:
                    seam_gap_gt_defect += 1

                if len(unlifted_samples) < args.samples and is_achiever:
                    path = bfs_path_bad(small, deleted, dprime)
                    if path is None:
                        raise RuntimeError("missing deleted path for unlifted achiever")
                    unlifted_samples.append(
                        UnliftedSample(
                            c=c,
                            deleted=deleted,
                            dprime=dprime,
                            fc_c=fc_c,
                            fc_dprime=fc_dprime,
                            defect=defect,
                            path=path,
                            seam_pred=best_pred,
                            seam_mover=best_mover,
                        )
                    )
            else:
                strategy_fail_pairs += 1
                source_has_strategy_fail = True
                if is_achiever:
                    achiever_strategy_fail_pairs += 1
                    source_has_achiever_strategy_fail = True
                if len(strategy_fail_samples) < args.samples:
                    path = bfs_path_bad(small, deleted, dprime)
                    if path is None:
                        raise RuntimeError("missing deleted path for strategy-failure target")
                    strategy_fail_samples.append(
                        UnliftedSample(
                            c=c,
                            deleted=deleted,
                            dprime=dprime,
                            fc_c=fc_c,
                            fc_dprime=fc_dprime,
                            defect=defect,
                            path=path,
                            seam_pred=None,
                            seam_mover=None,
                        )
                    )

        if any(small.fc_all[dprime] == phi_small for dprime in unlifted):
            sources_with_unlifted_achiever += 1
        if source_has_strategy_fail:
            strategy_fail_sources += 1
        if source_has_achiever_strategy_fail:
            achiever_strategy_fail_sources += 1

    print(f"Residual proof strategy scan at n={args.n}, k={args.k}")
    print(f"built TP graphs: n={big.n} bad={len(big.bad_configs)}, n-1={small.n} bad={len(small.bad_configs)}")
    print()

    print("TASK 2: exact lift versus unlifted deleted states")
    print(f"  sources checked: {total_sources}")
    print(f"  total deleted reachable pairs (c,d'): {total_pairs}")
    print(f"  lifted pairs with some d in S_n(c), delete(d)=d': {lifted_pairs}")
    print(f"  unlifted pairs: {unlifted_pairs}")
    print(f"  sources with at least one unlifted state: {sources_with_unlifted}")
    print(f"  unlifted Phi-achiever pairs: {unlifted_achiever_pairs}")
    print(f"  sources with an unlifted Phi-achiever: {sources_with_unlifted_achiever}")
    print(f"  unlifted pairs with fc(d') > fc(c): {unlifted_fc_violation}")
    print(f"  unlifted achievers with fc(d') > fc(c): {unlifted_achiever_fc_violation}")
    print("  distribution of max_d' fc(d') - fc(c) over unlifted states by source:")
    filtered = Counter({k: v for k, v in max_unlifted_delta.items() if k != -999})
    print(f"    {summarize_counter(filtered)}")
    if unlifted_samples:
        print("  sample unlifted Phi-achievers:")
        for idx, sample in enumerate(unlifted_samples, start=1):
            print(f"    [{idx}] c={format_cfg(sample.c)} fc(c)={sample.fc_c} defect={sample.defect}")
            print(f"         delete(c)={format_cfg(sample.deleted)}")
            print(f"         unlifted d'={format_cfg(sample.dprime)} fc(d')={sample.fc_dprime}")
            print(f"         deleted TP path movers={sample.path.movers}")
            if sample.seam_pred is not None:
                print(
                    f"         lifted seam predecessor={format_cfg(sample.seam_pred)} "
                    f"via mover {sample.seam_mover}"
                )
    print()

    print("TASK 3: proposed single-seam-step proof strategy")
    print("  claim tested on each unlifted pair:")
    print("    there is a lifted d'' with a single seam TP step d'' -> d'")
    print("    and fc(d') - fc(d'') <= 1 <= defect, or more directly <= defect")
    print(f"  unlifted pairs with a direct lifted seam predecessor: {direct_seam_pred_pairs} / {unlifted_pairs}")
    print(
        f"  unlifted Phi-achievers with a direct lifted seam predecessor: "
        f"{direct_seam_pred_achiever_pairs} / {unlifted_achiever_pairs}"
    )
    print(f"  strategy failures on all unlifted pairs: {strategy_fail_pairs} pairs across {strategy_fail_sources} sources")
    print(
        f"  strategy failures on unlifted achievers: "
        f"{achiever_strategy_fail_pairs} pairs across {achiever_strategy_fail_sources} sources"
    )
    print(f"  fc(d') - max_lifted_seam_pred_fc distribution: {summarize_counter(seam_gap)}")
    print(f"  direct seam cases with fc gap > 1: {seam_gap_gt_one}")
    print(f"  direct seam cases with fc gap > defect(c): {seam_gap_gt_defect}")
    if strategy_fail_samples:
        print("  sample strategy failures:")
        for idx, sample in enumerate(strategy_fail_samples, start=1):
            print(f"    [{idx}] c={format_cfg(sample.c)} fc(c)={sample.fc_c} defect={sample.defect}")
            print(f"         delete(c)={format_cfg(sample.deleted)}")
            print(f"         d'={format_cfg(sample.dprime)} fc(d')={sample.fc_dprime}")
            print(f"         deleted TP path movers={sample.path.movers}")
    print()

    print("TASK 4: simplest delete-image proof")
    print(f"  pairwise failures of delete(S_n(c)) ⊆ S_(n-1)(delete(c)): {delete_subset_pair_fail}")
    print(f"  source-wise failures of delete(S_n(c)) ⊆ S_(n-1)(delete(c)): {delete_subset_source_fail}")
    print("  seam-only side condition")
    print(f"    unlifted pairs with fc(d') <= fc(c): {unlifted_pairs - unlifted_fc_violation} / {unlifted_pairs}")
    print(
        f"    unlifted Phi-achievers with fc(d') <= fc(c): "
        f"{unlifted_achiever_pairs - unlifted_achiever_fc_violation} / {unlifted_achiever_pairs}"
    )
    if delete_subset_failure is not None:
        sample = delete_subset_failure
        print("  sample delete-image failure:")
        print(f"    c={format_cfg(sample.c)}")
        print(f"    delete(c)={format_cfg(sample.deleted_c)}")
        print(f"    d={format_cfg(sample.d)}")
        print(f"    delete(d)={format_cfg(sample.deleted_d)}")
        print(f"    big TP path movers={sample.path.movers}")
    print()

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
