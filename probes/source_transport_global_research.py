#!/usr/bin/env python3
"""Global source_transport research for n=9.

Uses the exact TP-bad graph model from `source_transport_seam_research.py`
and adds the four requested analyses:
1. Tight cases for PhiFull(delete(c)) = PhiFull(c) at k=4.
2. PhiFull achievers d' and matching size-9 witnesses d.
3. Exhaustive check of the weaker projected statement.
4. Residual-gap statistics for PhiFull = fc + slack.
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple


ROOT = os.path.dirname(__file__)
sys.path.insert(0, ROOT)

from source_transport_seam_research import (  # type: ignore
    Config,
    TpBadGraph,
    delete_config,
    format_cfg,
    good_cycle_configs,
    insert_value,
    valid_sites,
)


@dataclass(frozen=True)
class TightRecord:
    c: Config
    deleted: Config
    phi_big: int
    phi_small: int
    fc_big: int
    fc_small: int
    defect: int
    g_big: int
    g_small: int
    dist_big: int
    dist_small: int
    local_triple: Tuple[int, int, int]
    is_good_big: bool
    is_good_small: bool


@dataclass
class PathResult:
    nodes: List[Config]
    movers: List[int]

    @property
    def length(self) -> int:
        return len(self.movers)


def deep_site_states(_: int) -> range:
    return range(3)


def build_bad_step_distance(n: int) -> Dict[Config, int]:
    good = good_cycle_configs(n)
    graph = TpBadGraph(n)
    rev: Dict[Config, List[Config]] = defaultdict(list)
    dist: Dict[Config, int] = {}
    q: deque[Config] = deque()

    for g in good:
        dist[g] = 0
        q.append(g)

    for src in graph.all_configs:
        if src in good:
            continue
        for mover in range(n):
            left = src[(mover - 1) % n]
            self_val = src[mover]
            right = src[(mover + 1) % n]
            out = graph.fs[mover](left, self_val, right)
            if out == self_val:
                continue
            dst = list(src)
            dst[mover] = out
            rev[tuple(dst)].append(src)

    while q:
        node = q.popleft()
        for prv in rev.get(node, []):
            if prv not in dist:
                dist[prv] = dist[node] + 1
                q.append(prv)

    missing = [cfg for cfg in graph.all_configs if cfg not in dist]
    if missing:
        raise RuntimeError(f"distance-to-good missing for {len(missing)} configs at n={n}")
    return dist


def topo_order_from_scc(graph: TpBadGraph) -> List[int]:
    graph.ensure_scc()
    indeg = [len(preds) for preds in graph.comp_rev]
    q = deque([cid for cid, deg in enumerate(indeg) if deg == 0])
    topo: List[int] = []
    while q:
        cid = q.popleft()
        topo.append(cid)
        for nxt in graph.comp_succ[cid]:
            indeg[nxt] -= 1
            if indeg[nxt] == 0:
                q.append(nxt)
    if len(topo) != len(graph.comp_nodes):
        raise RuntimeError("SCC condensation is not a DAG")
    return topo


def component_desc_bits(graph: TpBadGraph) -> List[int]:
    graph.ensure_scc()
    topo = topo_order_from_scc(graph)
    bits = [0] * len(graph.comp_nodes)
    for cid in reversed(topo):
        acc = 1 << cid
        for nxt in graph.comp_succ[cid]:
            acc |= bits[nxt]
        bits[cid] = acc
    return bits


def iter_bits(bits: int) -> Iterable[int]:
    while bits:
        lsb = bits & -bits
        yield lsb.bit_length() - 1
        bits ^= lsb


def reachable_bad_nodes(graph: TpBadGraph, desc_bits: List[int], cfg: Config) -> List[Config]:
    if cfg in graph.good_cycle:
        return [cfg]
    src_id = graph.bad_id[cfg]
    bits = desc_bits[graph.comp_of[src_id]]
    out: List[Config] = []
    for cid in iter_bits(bits):
        for node in graph.comp_nodes[cid]:
            out.append(graph.bad_configs[node])
    return out


def reachable_bad_ids(graph: TpBadGraph, src: Config) -> Set[int]:
    if src in graph.good_cycle:
        return set()
    start = graph.bad_id[src]
    seen = {start}
    q = deque([start])
    while q:
        node = q.popleft()
        for nxt, _ in graph.out_edges[node]:
            if nxt not in seen:
                seen.add(nxt)
                q.append(nxt)
    return seen


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
    cur = target_id
    while cur is not None:
        ids.append(cur)
        prev, mover = parent[cur]
        if mover is not None:
            movers.append(mover)
        cur = prev
    ids.reverse()
    movers.reverse()
    return PathResult(nodes=[graph.bad_configs[i] for i in ids], movers=movers)


def small_path(graph: TpBadGraph, src: Config, target: Config) -> Optional[PathResult]:
    if src == target:
        return PathResult(nodes=[src], movers=[])
    if src in graph.good_cycle or target in graph.good_cycle:
        return None
    return bfs_path_bad(graph, src, target)


def target_bits_for_direct(big: TpBadGraph, deleted_target: Config, k: int, min_fc: int) -> Tuple[int, List[Config]]:
    bits = 0
    lifted_configs: List[Config] = []
    for x in deep_site_states(k):
        lifted = insert_value(deleted_target, k, x)
        if big.fc_all[lifted] < min_fc:
            continue
        lifted_configs.append(lifted)
        if lifted not in big.good_cycle:
            bits |= 1 << big.comp_of[big.bad_id[lifted]]
    return bits, lifted_configs


def projected_target_bits(
    big: TpBadGraph,
    small: TpBadGraph,
    k: int,
    desc_bits_small: List[int],
) -> Dict[Tuple[int, int], int]:
    cache: Dict[Tuple[int, int], int] = {}
    nodes_by_comp = [[small.bad_configs[node] for node in nodes] for nodes in small.comp_nodes]
    for cid in range(len(small.comp_nodes)):
        descendants: List[Config] = []
        for sid in iter_bits(desc_bits_small[cid]):
            descendants.extend(nodes_by_comp[sid])
        for threshold in range(big.n + 1):
            bits = 0
            for cfg in descendants:
                for x in deep_site_states(k):
                    lifted = insert_value(cfg, k, x)
                    if big.fc_all[lifted] < threshold or lifted in big.good_cycle:
                        continue
                    bits |= 1 << big.comp_of[big.bad_id[lifted]]
            cache[(cid, threshold)] = bits
    return cache


def find_exact_big_witness(big: TpBadGraph, src: Config, dprime: Config, k: int, min_fc: int) -> Optional[Config]:
    if src in big.good_cycle:
        return src if delete_config(src, k) == dprime and big.fc_all[src] >= min_fc else None
    reachable = reachable_bad_ids(big, src)
    best_cfg: Optional[Config] = None
    best_len: Optional[int] = None
    for x in deep_site_states(k):
        lifted = insert_value(dprime, k, x)
        if lifted in big.good_cycle or big.fc_all[lifted] < min_fc:
            continue
        if big.bad_id[lifted] not in reachable:
            continue
        path = bfs_path_bad(big, src, lifted)
        if path is None:
            continue
        if best_cfg is None or path.length < best_len or (path.length == best_len and lifted < best_cfg):
            best_cfg = lifted
            best_len = path.length
    return best_cfg


def find_projected_big_witness(
    big: TpBadGraph,
    small: TpBadGraph,
    src_big: Config,
    achiever: Config,
    k: int,
    min_fc: int,
    desc_bits_small: List[int],
) -> Optional[Tuple[Config, Config, PathResult, PathResult]]:
    if src_big in big.good_cycle:
        deleted_src = delete_config(src_big, k)
        if big.fc_all[src_big] < min_fc:
            return None
        if deleted_src == achiever:
            return src_big, deleted_src, PathResult([src_big], []), PathResult([achiever], [])
        lag = small_path(small, achiever, deleted_src)
        if lag is None:
            return None
        return src_big, deleted_src, PathResult([src_big], []), lag

    reachable = reachable_bad_ids(big, src_big)
    descendants = reachable_bad_nodes(small, desc_bits_small, achiever)
    best = None
    best_key = None

    for projected in descendants:
        for x in deep_site_states(k):
            lifted = insert_value(projected, k, x)
            if lifted in big.good_cycle or big.fc_all[lifted] < min_fc:
                continue
            if big.bad_id[lifted] not in reachable:
                continue
            big_path = bfs_path_bad(big, src_big, lifted)
            lag = small_path(small, achiever, projected)
            if big_path is None or lag is None:
                continue
            key = (lag.length, big_path.length, projected, lifted)
            if best_key is None or key < best_key:
                best_key = key
                best = (lifted, projected, big_path, lag)
    return best


def summarize_counter(counter: Counter[int]) -> str:
    return ", ".join(f"{k}:{counter[k]}" for k in sorted(counter))


def top_items(counter: Counter, limit: int = 10) -> str:
    return ", ".join(f"{key}:{val}" for key, val in counter.most_common(limit))


def task1_tight_cases(
    big: TpBadGraph,
    small: TpBadGraph,
    k: int,
    dist_big: Dict[Config, int],
    dist_small: Dict[Config, int],
) -> List[TightRecord]:
    tight: List[TightRecord] = []
    for c in big.all_configs:
        deleted = delete_config(c, k)
        phi_big = big.phi_of(c)
        phi_small = small.phi_of(deleted)
        if phi_big != phi_small:
            continue
        fc_big = big.fc_all[c]
        fc_small = small.fc_all[deleted]
        tight.append(
            TightRecord(
                c=c,
                deleted=deleted,
                phi_big=phi_big,
                phi_small=phi_small,
                fc_big=fc_big,
                fc_small=fc_small,
                defect=fc_big - fc_small,
                g_big=phi_big - fc_big,
                g_small=phi_small - fc_small,
                dist_big=dist_big[c],
                dist_small=dist_small[deleted],
                local_triple=(c[k - 1], c[k], c[k + 1]),
                is_good_big=c in big.good_cycle,
                is_good_small=deleted in small.good_cycle,
            )
        )

    print(f"TASK 1, n=9 k={k}")
    print(f"  tight configs: {len(tight)} / {len(big.all_configs)}")
    print(f"  good at n: {sum(rec.is_good_big for rec in tight)}")
    print(f"  good after delete: {sum(rec.is_good_small for rec in tight)}")
    print(f"  distinct deleted configs among tight cases: {len({rec.deleted for rec in tight})}")
    print(f"  deletion defect: {summarize_counter(Counter(rec.defect for rec in tight))}")
    print(f"  big slack g=Phi-fc: {summarize_counter(Counter(rec.g_big for rec in tight))}")
    print(f"  small slack g=Phi-fc: {summarize_counter(Counter(rec.g_small for rec in tight))}")
    print(f"  distance-to-good at n: {summarize_counter(Counter(rec.dist_big for rec in tight))}")
    print(f"  distance-to-good at n-1: {summarize_counter(Counter(rec.dist_small for rec in tight))}")
    print(f"  top local triples around k: {top_items(Counter(rec.local_triple for rec in tight))}")
    print()
    return tight


def task2_achievers(big: TpBadGraph, small: TpBadGraph, k: int, tight: List[TightRecord]) -> None:
    desc_bits_small = component_desc_bits(small)
    tight_bad = [rec for rec in tight if not rec.is_good_big and not rec.is_good_small]
    achiever_pairs = 0
    direct_pairs = 0
    projected_pairs = 0
    fail_pairs = 0
    lag_dist = Counter()
    path_dist = Counter()
    seam_move_dist = Counter()
    examples = []

    for rec in tight_bad:
        reachable_small = reachable_bad_nodes(small, desc_bits_small, rec.deleted)
        achievers = [cfg for cfg in reachable_small if small.fc_all[cfg] == rec.phi_small]
        for achiever in achievers:
            achiever_pairs += 1
            exact = find_exact_big_witness(big, rec.c, achiever, k, rec.phi_small)
            if exact is not None:
                direct_pairs += 1
                path = bfs_path_bad(big, rec.c, exact)
                if path is None:
                    raise RuntimeError("missing path for exact witness")
                lag = PathResult([achiever], [])
                lag_dist[0] += 1
                path_dist[path.length] += 1
                seam_move_dist[sum(1 for m in path.movers if m in (k - 1, k, k + 1))] += 1
                if len(examples) < 5:
                    examples.append((rec, achiever, exact, achiever, path, lag))
                continue

            projected = find_projected_big_witness(big, small, rec.c, achiever, k, rec.phi_small, desc_bits_small)
            if projected is None:
                fail_pairs += 1
                continue
            projected_pairs += 1
            lifted, projected_small, path, lag = projected
            lag_dist[lag.length] += 1
            path_dist[path.length] += 1
            seam_move_dist[sum(1 for m in path.movers if m in (k - 1, k, k + 1))] += 1
            if len(examples) < 5:
                examples.append((rec, achiever, lifted, projected_small, path, lag))

    print(f"TASK 2, n=9 k={k}")
    print(f"  tight bad cases: {len(tight_bad)}")
    print(f"  achiever pairs checked: {achiever_pairs}")
    print(f"  direct witnesses delete(d)=d': {direct_pairs}")
    print(f"  projected witnesses: {projected_pairs}")
    print(f"  failures: {fail_pairs}")
    print(f"  lag distance d' -> delete(d): {summarize_counter(lag_dist)}")
    print(f"  big TP path length c -> d: {summarize_counter(path_dist)}")
    print(f"  seam-move count on chosen big path: {summarize_counter(seam_move_dist)}")
    print("  representative cases:")
    for idx, (rec, achiever, witness, projected_small, path, lag) in enumerate(examples, start=1):
        relation = "exact" if achiever == projected_small else f"projected(+{lag.length})"
        print(f"    [{idx}] c={format_cfg(rec.c)} delete(c)={format_cfg(rec.deleted)} phi={rec.phi_big}")
        print(f"         achiever d'={format_cfg(achiever)}")
        print(f"         witness d={format_cfg(witness)} delete(d)={format_cfg(projected_small)} {relation}")
        print(f"         big movers={path.movers} lag movers={lag.movers}")
    print()


def task3_weaker_statement(big: TpBadGraph, small: TpBadGraph, ks: Sequence[int]) -> None:
    desc_bits_big = component_desc_bits(big)
    desc_bits_small = component_desc_bits(small)

    for k in ks:
        proj_bits = projected_target_bits(big, small, k, desc_bits_small)
        total_pairs = 0
        bad_source_pairs = 0
        direct_fail = 0
        weak_fail = 0
        weak_fail_bad_source = 0
        sample_direct = None
        sample_weak = None

        for c in big.all_configs:
            deleted = delete_config(c, k)
            dprimes = [deleted] if deleted in small.good_cycle else reachable_bad_nodes(small, desc_bits_small, deleted)
            source_is_bad = c not in big.good_cycle
            source_bits = 0
            if source_is_bad:
                source_bits = desc_bits_big[big.comp_of[big.bad_id[c]]]

            for dprime in dprimes:
                total_pairs += 1
                if source_is_bad:
                    bad_source_pairs += 1
                threshold = small.fc_all[dprime]
                direct_bits, direct_lifts = target_bits_for_direct(big, dprime, k, threshold)

                if source_is_bad:
                    direct_ok = bool(source_bits & direct_bits)
                else:
                    direct_ok = any(lift == c and big.fc_all[lift] >= threshold for lift in direct_lifts)
                if not direct_ok:
                    direct_fail += 1
                    if sample_direct is None:
                        sample_direct = (c, deleted, dprime)

                if source_is_bad:
                    if dprime in small.good_cycle:
                        weak_ok = False
                    else:
                        weak_ok = bool(source_bits & proj_bits[(small.comp_of[small.bad_id[dprime]], threshold)])
                else:
                    deleted_c = delete_config(c, k)
                    weak_ok = big.fc_all[c] >= threshold and (
                        deleted_c == dprime or
                        (dprime not in small.good_cycle and small_path(small, dprime, deleted_c) is not None)
                    )
                if not weak_ok:
                    weak_fail += 1
                    if source_is_bad:
                        weak_fail_bad_source += 1
                    if sample_weak is None:
                        sample_weak = (c, deleted, dprime)

        print(f"TASK 3, n=9 k={k}")
        print(f"  all reachable pairs (c,d'): {total_pairs}")
        print(f"  bad-source pairs only: {bad_source_pairs}")
        print(f"  direct global-lift failures: {direct_fail}")
        print(f"  weak projected-lift failures: {weak_fail}")
        print(f"  weak projected-lift failures with bad source c: {weak_fail_bad_source}")
        if sample_direct is not None:
            c, deleted, dprime = sample_direct
            print(f"  sample direct failure: c={format_cfg(c)} delete(c)={format_cfg(deleted)} d'={format_cfg(dprime)}")
        if sample_weak is not None:
            c, deleted, dprime = sample_weak
            print(f"  sample weak failure: c={format_cfg(c)} delete(c)={format_cfg(deleted)} d'={format_cfg(dprime)}")
        print()


def task4_gap_decomposition(big: TpBadGraph, small: TpBadGraph, ks: Sequence[int]) -> None:
    for k in ks:
        r_dist = Counter()
        defect_dist = Counter()
        big_slack_dist = Counter()
        residual_dist = Counter()
        r_gt_defect = 0
        residual_gt_defect = 0
        tight_count = 0

        for c in big.all_configs:
            deleted = delete_config(c, k)
            phi_big = big.phi_of(c)
            phi_small = small.phi_of(deleted)
            fc_big = big.fc_all[c]
            fc_small = small.fc_all[deleted]
            big_slack = phi_big - fc_big
            r = phi_small - fc_small
            defect = fc_big - fc_small
            residual = r - big_slack

            r_dist[r] += 1
            defect_dist[defect] += 1
            big_slack_dist[big_slack] += 1
            residual_dist[residual] += 1

            if r > defect:
                r_gt_defect += 1
            if residual > defect:
                residual_gt_defect += 1
            if phi_big == phi_small:
                tight_count += 1

        print(f"TASK 4, n=9 k={k}")
        print(f"  R = Phi(delete(c)) - fc(delete(c)): {summarize_counter(r_dist)}")
        print(f"  deletion defect: {summarize_counter(defect_dist)}")
        print(f"  big slack g_n(c): {summarize_counter(big_slack_dist)}")
        print(f"  residual R - g_n(c): {summarize_counter(residual_dist)}")
        print(f"  cases with R > defect: {r_gt_defect}")
        print(f"  cases with R - g_n(c) > defect: {residual_gt_defect}")
        print(f"  tight equality cases: {tight_count}")
        print()


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=9)
    parser.add_argument("--focus-k", type=int, default=4)
    parser.add_argument("--ks", type=int, nargs="+", default=[4, 5])
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)
    if args.n != 9:
        raise SystemExit("This script is specialized to n=9.")
    if args.focus_k not in valid_sites(args.n):
        raise SystemExit(f"focus-k must be one of {valid_sites(args.n)}")

    big = TpBadGraph(args.n)
    small = TpBadGraph(args.n - 1)
    big.ensure_scc()
    small.ensure_scc()

    print(f"built TP graphs: n={big.n} bad={len(big.bad_configs)}, n-1={small.n} bad={len(small.bad_configs)}")
    print("computing shortest bad-step distances to good cycle...")
    dist_big = build_bad_step_distance(big.n)
    dist_small = build_bad_step_distance(small.n)
    print()

    tight = task1_tight_cases(big, small, args.focus_k, dist_big, dist_small)
    task2_achievers(big, small, args.focus_k, tight)
    task3_weaker_statement(big, small, args.ks)
    task4_gap_decomposition(big, small, args.ks)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
