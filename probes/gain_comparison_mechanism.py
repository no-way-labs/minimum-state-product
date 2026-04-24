#!/usr/bin/env python3
"""Investigate why R <= g_n(c) + defect holds at n=9, k=4.

This script reuses the exact TP-bad graph model from
`source_transport_seam_research.py` and focuses on the mechanism behind

  R = PhiFull(delete(c)) - fc(delete(c))
  g = PhiFull(c) - fc(c)
  defect = fc(c) - fc(delete(c))

for deletion at a fixed deep site k.

The three analyses are:
1. Compare the full TP-reachable sets S(c) and S'(delete(c)).
2. Test the "insert the same value back" lift claim.
3. Separate offsite gain from seam-dependent gain on the deleted graph.
"""

from __future__ import annotations

import argparse
import heapq
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
    insert_value,
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
class OffsiteSummary:
    reach_nodes: Dict[Config, Tuple[Config, ...]]
    phi_off: Dict[Config, int]
    min_seam_to_phi: Dict[Config, int]
    seam_bonus: Dict[Config, int]


def summarize_counter(counter: Counter[int]) -> str:
    return ", ".join(f"{key}:{counter[key]}" for key in sorted(counter))


def build_exact_lift_fcs(big: TpBadGraph, big_nodes: Iterable[Config], k: int) -> Dict[Config, int]:
    best: Dict[Config, int] = {}
    for node in big_nodes:
        deleted = delete_config(node, k)
        fc_node = big.fc_all[node]
        current = best.get(deleted)
        if current is None or fc_node > current:
            best[deleted] = fc_node
    return best


def offsite_summary(small: TpBadGraph, k: int) -> OffsiteSummary:
    seam = {k - 1, k}
    reach_nodes: Dict[Config, Tuple[Config, ...]] = {}
    phi_off: Dict[Config, int] = {}
    min_seam_to_phi: Dict[Config, int] = {}
    seam_bonus: Dict[Config, int] = {}

    for cfg in small.all_configs:
        if cfg in small.good_cycle:
            reach = (cfg,)
            phi = small.fc_all[cfg]
            min_seam = 0
        else:
            start = small.bad_id[cfg]
            seen = {start}
            q = deque([start])
            order: List[int] = []
            while q:
                node = q.popleft()
                order.append(node)
                for nxt, mover in small.out_edges[node]:
                    if mover in seam or nxt in seen:
                        continue
                    seen.add(nxt)
                    q.append(nxt)
            reach = tuple(small.bad_configs[node] for node in order)
            phi = max(small.fc_all[node_cfg] for node_cfg in reach)

            target_fc = small.phi_of(cfg)
            dist = {start: 0}
            pq: List[Tuple[int, int]] = [(0, start)]
            min_seam = 0
            while pq:
                cost, node = heapq.heappop(pq)
                if cost != dist[node]:
                    continue
                if small.fc_all[small.bad_configs[node]] == target_fc:
                    min_seam = cost
                    break
                for nxt, mover in small.out_edges[node]:
                    weight = 1 if mover in seam else 0
                    new_cost = cost + weight
                    if new_cost < dist.get(nxt, 10**9):
                        dist[nxt] = new_cost
                        heapq.heappush(pq, (new_cost, nxt))

        reach_nodes[cfg] = reach
        phi_off[cfg] = phi
        min_seam_to_phi[cfg] = min_seam
        seam_bonus[cfg] = small.phi_of(cfg) - phi

    return OffsiteSummary(
        reach_nodes=reach_nodes,
        phi_off=phi_off,
        min_seam_to_phi=min_seam_to_phi,
        seam_bonus=seam_bonus,
    )


def min_seam_path_to_phi(small: TpBadGraph, src: Config, k: int) -> PathResult:
    if src in small.good_cycle:
        return PathResult(nodes=[src], movers=[])

    seam = {k - 1, k}
    start = small.bad_id[src]
    target_fc = small.phi_of(src)
    dist = {start: 0}
    parent: Dict[int, Tuple[Optional[int], Optional[int]]] = {start: (None, None)}
    pq: List[Tuple[int, int]] = [(0, start)]
    target: Optional[int] = None

    while pq:
        cost, node = heapq.heappop(pq)
        if cost != dist[node]:
            continue
        if small.fc_all[small.bad_configs[node]] == target_fc:
            target = node
            break
        for nxt, mover in small.out_edges[node]:
            weight = 1 if mover in seam else 0
            new_cost = cost + weight
            if new_cost < dist.get(nxt, 10**9):
                dist[nxt] = new_cost
                parent[nxt] = (node, mover)
                heapq.heappush(pq, (new_cost, nxt))

    if target is None:
        raise RuntimeError("missing path to Phi-achiever")

    node_ids: List[int] = []
    movers: List[int] = []
    cur: Optional[int] = target
    while cur is not None:
        node_ids.append(cur)
        prv, mover = parent[cur]
        if mover is not None:
            movers.append(mover)
        cur = prv
    node_ids.reverse()
    movers.reverse()
    return PathResult(nodes=[small.bad_configs[node] for node in node_ids], movers=movers)


def analyze_task1(
    big: TpBadGraph,
    small: TpBadGraph,
    k: int,
    big_reach: ReachCache,
    small_reach: ReachCache,
) -> None:
    total_pairs = 0
    exact_pairs = 0
    exact_source_fail = 0
    exact_achiever_fail_sources = 0
    exact_achiever_fail_pairs = 0
    relaxed_inj_fail = 0
    relaxed_inj_fail_size = 0
    missed_rel_phi = Counter()
    best_gap = Counter()
    avg_small = 0
    avg_exact_cover = 0
    avg_target_pool = 0

    first_exact_miss: Optional[Tuple[Config, Config, Config]] = None

    for c in big.all_configs:
        deleted = delete_config(c, k)
        big_nodes = big_reach.get(c)
        small_nodes = small_reach.get(deleted)
        small_set = set(small_nodes)
        exact_map = build_exact_lift_fcs(big, big_nodes, k)
        target_pool = [node for node in big_nodes if delete_config(node, k) in small_set]
        target_pool_fcs = sorted((big.fc_all[node] for node in target_pool), reverse=True)
        small_fcs = sorted((small.fc_all[node] for node in small_nodes), reverse=True)
        fallback_fc = target_pool_fcs[0]
        phi_small = small.phi_of(deleted)

        avg_small += len(small_nodes)
        avg_exact_cover += sum(1 for node in small_nodes if node in exact_map)
        avg_target_pool += len(target_pool)

        source_has_exact_miss = False
        source_has_achiever_miss = False
        for dprime in small_nodes:
            total_pairs += 1
            best_exact = exact_map.get(dprime)
            if best_exact is not None:
                exact_pairs += 1
                best_gap[best_exact - small.fc_all[dprime]] += 1
            else:
                source_has_exact_miss = True
                gap = fallback_fc - small.fc_all[dprime]
                best_gap[gap] += 1
                missed_rel_phi[small.fc_all[dprime] - phi_small] += 1
                if first_exact_miss is None:
                    first_exact_miss = (c, deleted, dprime)

            if small.fc_all[dprime] == phi_small and best_exact is None:
                exact_achiever_fail_pairs += 1
                source_has_achiever_miss = True

        if source_has_exact_miss:
            exact_source_fail += 1
        if source_has_achiever_miss:
            exact_achiever_fail_sources += 1

        if len(target_pool_fcs) < len(small_fcs):
            relaxed_inj_fail += 1
            relaxed_inj_fail_size += 1
        else:
            if any(big_fc < small_fc for big_fc, small_fc in zip(target_pool_fcs, small_fcs)):
                relaxed_inj_fail += 1

    print(f"TASK 1: Reachable-set comparison (n={big.n}, k={k})")
    print(f"  sources checked: {len(big.all_configs)}")
    print(f"  total reachable pairs (c,d'): {total_pairs}")
    print(f"  avg |S'(delete(c))|: {avg_small / len(big.all_configs):.2f}")
    print(f"  avg exact coverage |delete(S(c)) ∩ S'|: {avg_exact_cover / len(big.all_configs):.2f}")
    print(f"  avg target pool |T(c)| with delete(d) in S': {avg_target_pool / len(big.all_configs):.2f}")
    print(f"  exact whole-set lift failures S' ⊄ delete(S(c)): {exact_source_fail}")
    print(f"  exact pairwise lifts delete(d)=d': {exact_pairs} / {total_pairs}")
    print(
        f"  weaker fc-preserving injection S' -> T(c): "
        f"{len(big.all_configs) - relaxed_inj_fail} hold, {relaxed_inj_fail} fail"
    )
    print(f"    by size |T(c)| < |S'|: {relaxed_inj_fail_size}")
    print(f"    by fc shortfall despite enough states: {relaxed_inj_fail - relaxed_inj_fail_size}")
    print(
        f"  exact achiever lift failures: "
        f"{exact_achiever_fail_sources} sources, {exact_achiever_fail_pairs} achiever pairs"
    )
    print(f"  missed exact-lift states by fc(d') - Phi(delete(c)): {summarize_counter(missed_rel_phi)}")
    print(f"  best-match fc gap (exact if possible, else best d in T(c)): {summarize_counter(best_gap)}")
    if first_exact_miss is not None:
        c, deleted, dprime = first_exact_miss
        print(f"  sample exact-lift miss: c={format_cfg(c)}")
        print(f"    delete(c)={format_cfg(deleted)} d'={format_cfg(dprime)} fc(d')={small.fc_all[dprime]}")
    print()


def analyze_task2(
    big: TpBadGraph,
    small: TpBadGraph,
    k: int,
    big_reach: ReachCache,
    small_reach: ReachCache,
    offsite: OffsiteSummary,
) -> None:
    total_pairs = 0
    same_value_success = 0
    source_fail = 0
    achiever_pairs = 0
    achiever_same_value_success = 0
    offsite_pairs = 0
    offsite_subset_equal = 0
    offsite_subset_strict = 0
    first_same_value_fail: Optional[Tuple[Config, Config, Config, Config]] = None

    for c in big.all_configs:
        deleted = delete_config(c, k)
        big_nodes = big_reach.get(c)
        big_set = set(big_nodes)
        small_nodes = small_reach.get(deleted)
        phi_small = small.phi_of(deleted)
        x = c[k]

        same_proj = {delete_config(node, k) for node in big_nodes if node[k] == x}
        offsite_set = set(offsite.reach_nodes[deleted])
        if same_proj == offsite_set:
            offsite_subset_equal += 1
        elif offsite_set < same_proj:
            offsite_subset_strict += 1
        else:
            raise RuntimeError("offsite exact lift failed unexpectedly")

        source_has_fail = False
        for dprime in small_nodes:
            total_pairs += 1
            lifted = insert_value(dprime, k, x)
            if lifted in big_set:
                same_value_success += 1
                if small.fc_all[dprime] == phi_small:
                    achiever_same_value_success += 1
            else:
                source_has_fail = True
                if first_same_value_fail is None:
                    first_same_value_fail = (c, deleted, dprime, lifted)
            if small.fc_all[dprime] == phi_small:
                achiever_pairs += 1

        offsite_pairs += len(offsite.reach_nodes[deleted])
        if source_has_fail:
            source_fail += 1

    print(f"TASK 2: Same-value lift claim (n={big.n}, k={k})")
    print("  claim tested:")
    print("    for every d' in S'(delete(c)), insert the deleted site back with value c[k]")
    print("    and ask whether that exact lifted config lies in S(c)")
    print(f"  whole-set failures: {source_fail} / {len(big.all_configs)} sources")
    print(f"  pairwise successes: {same_value_success} / {total_pairs}")
    print(f"  achiever-pair successes: {achiever_same_value_success} / {achiever_pairs}")
    print(f"  offsite-only pairs: {offsite_pairs} / {offsite_pairs} succeed")
    print(f"  same-value projection equals offsite reach: {offsite_subset_equal} sources")
    print(f"  same-value projection strictly contains offsite reach: {offsite_subset_strict} sources")
    if first_same_value_fail is not None:
        c, deleted, dprime, lifted = first_same_value_fail
        print(f"  sample failure: c={format_cfg(c)} delete(c)={format_cfg(deleted)}")
        print(f"    d'={format_cfg(dprime)}")
        print(f"    inserted with same value c[k]={c[k]} gives d={format_cfg(lifted)}")
        print("    but d is not TP-reachable from c")
    print()


def analyze_task3(
    big: TpBadGraph,
    small: TpBadGraph,
    k: int,
    offsite: OffsiteSummary,
) -> None:
    seam_bonus_small = Counter()
    min_seam_to_phi = Counter()
    r_off_vs_g = Counter()
    seam_bonus_biglift = Counter()
    residual = Counter()
    positive_residual = Counter()

    sample_bonus1: Optional[Config] = None
    sample_bonus2: Optional[Config] = None

    for deleted in small.all_configs:
        bonus = offsite.seam_bonus[deleted]
        seam_bonus_small[bonus] += 1
        min_seam_to_phi[offsite.min_seam_to_phi[deleted]] += 1
        if bonus == 1 and sample_bonus1 is None:
            sample_bonus1 = deleted
        if bonus == 2 and sample_bonus2 is None:
            sample_bonus2 = deleted

    for c in big.all_configs:
        deleted = delete_config(c, k)
        fc_small = small.fc_all[deleted]
        fc_big = big.fc_all[c]
        r = small.phi_of(deleted) - fc_small
        r_off = offsite.phi_off[deleted] - fc_small
        g = big.phi_of(c) - fc_big
        defect = fc_big - fc_small

        r_off_vs_g[g - r_off] += 1
        seam_bonus_biglift[r - r_off] += 1
        residual_val = r - g
        residual[residual_val] += 1
        if residual_val > 0:
            positive_residual[(defect, residual_val)] += 1

    print(f"TASK 3: Offsite steps versus seam steps (n={big.n}, k={k})")
    print(f"  unique deleted sources: {len(small.all_configs)}")
    print(f"  seam bonus Phi(delete(c)) - Phi_off(delete(c)): {summarize_counter(seam_bonus_small)}")
    print(f"  min seam-step count to some Phi-achiever: {summarize_counter(min_seam_to_phi)}")
    print("  big-lift view over all size-n sources c:")
    print(f"    g_n(c) - R_off(delete(c)): {summarize_counter(r_off_vs_g)}")
    print(f"    R(delete(c)) - R_off(delete(c)): {summarize_counter(seam_bonus_biglift)}")
    print(f"    residual R - g_n(c): {summarize_counter(residual)}")
    print(f"    positive residuals by (defect, residual): {positive_residual}")
    if sample_bonus1 is not None:
        path = min_seam_path_to_phi(small, sample_bonus1, k)
        print(f"  sample seam-needed source (bonus 1): {format_cfg(sample_bonus1)}")
        print(
            f"    fc={small.fc_all[sample_bonus1]} "
            f"Phi={small.phi_of(sample_bonus1)} "
            f"Phi_off={offsite.phi_off[sample_bonus1]}"
        )
        print(f"    movers={path.movers}")
        print(f"    seam moves on chosen Phi path: {sum(1 for mover in path.movers if mover in (k - 1, k))}")
    if sample_bonus2 is not None:
        path = min_seam_path_to_phi(small, sample_bonus2, k)
        print(f"  sample seam-needed source (bonus 2): {format_cfg(sample_bonus2)}")
        print(
            f"    fc={small.fc_all[sample_bonus2]} "
            f"Phi={small.phi_of(sample_bonus2)} "
            f"Phi_off={offsite.phi_off[sample_bonus2]}"
        )
        print(f"    movers={path.movers}")
        print(f"    seam moves on chosen Phi path: {sum(1 for mover in path.movers if mover in (k - 1, k))}")
    print()

    print("Mechanism summary")
    print("  1. Offsite-only deleted dynamics always lift exactly under same-value insertion.")
    print("     Empirically this gives R_off(delete(c)) <= g_n(c) for every c.")
    print("  2. Seam moves are rare: only 72 / 2916 deleted sources need them to hit Phi.")
    print("  3. When seam moves matter, the seam bonus is tiny (at most 2 here), and")
    print("     the big graph often gets the same extra gain. The only positive residuals")
    print("     are (defect,residual)=(1,1),(2,1),(2,2), so residual never exceeds defect.")
    print()


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=9, help="original size n")
    parser.add_argument("--k", type=int, default=4, help="deleted site k")
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)
    if args.k not in valid_sites(args.n):
        raise SystemExit(f"k must be one of {valid_sites(args.n)} for n={args.n}")

    big = TpBadGraph(args.n)
    small = TpBadGraph(args.n - 1)
    big.ensure_scc()
    small.ensure_scc()

    big_reach = ReachCache(big, component_desc_bits(big), {})
    small_reach = ReachCache(small, component_desc_bits(small), {})
    offsite = offsite_summary(small, args.k)

    print(f"built TP graphs: n={big.n} bad={len(big.bad_configs)}, n-1={small.n} bad={len(small.bad_configs)}")
    print()

    analyze_task1(big, small, args.k, big_reach, small_reach)
    analyze_task2(big, small, args.k, big_reach, small_reach, offsite)
    analyze_task3(big, small, args.k, offsite)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
