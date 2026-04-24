#!/usr/bin/env python3
"""Analyze the residual bound behind `source_transport_residual_le`.

Focuses on the concrete case requested in the prompt:
  n = 9, k = 4.

For each size-9 source c with positive residual

  residual(c) =
    (PhiFull(delete(c)) - fc(delete(c))) - (PhiFull(c) - fc(c)),

the script:
1. Finds a canonical TP path at size n-1 from delete(c) to a Phi-achiever.
2. Identifies where that path first exceeds
   - the offsite-only bound Phi_off(delete(c)), and
   - the size-9 liftable bound fc(delete(c)) + g_n(c).
3. Checks whether those "excess" states have any good-cycle lift at size n.
4. Checks the literal "deleted from the cycle" hypothesis.
5. Checks the stronger global inequality PhiFull(delete(c)) <= fc(c).

The TP graph / Phi / good-cycle model is imported from the existing
research scripts under `lean/probes/`.
"""

from __future__ import annotations

import argparse
import heapq
import json
import os
import sys
from collections import Counter
from dataclasses import asdict, dataclass
from typing import Dict, List, Optional, Sequence, Tuple


THIS_DIR = os.path.dirname(os.path.abspath(__file__))
PAPER2_DIR = os.path.dirname(THIS_DIR)
LEAN_CLAUDE_DIR = os.path.join(PAPER2_DIR, "lean", "this project", "claude")
sys.path.insert(0, LEAN_CLAUDE_DIR)

from gain_comparison_mechanism import offsite_summary  # type: ignore
from source_transport_seam_research import (  # type: ignore
    Config,
    TpBadGraph,
    delete_config,
    format_cfg,
    insert_value,
)


@dataclass
class WitnessPoint:
    index: int
    cfg: Config
    fc: int
    good_lifts: List[Config]

    @property
    def has_good_lift(self) -> bool:
        return bool(self.good_lifts)


@dataclass
class ResidualRecord:
    c: Config
    deleted: Config
    fc_big: int
    phi_big: int
    g_big: int
    fc_small: int
    phi_small: int
    phi_off: int
    r_small: int
    r_off: int
    residual: int
    seam_bonus: int
    defect: int
    path_nodes: List[Config]
    path_movers: List[int]
    path_fcs: List[int]
    path_seam_moves: int
    first_offsite_excess: WitnessPoint
    first_residual_excess: WitnessPoint
    achiever_good_lifts: List[Config]
    any_good_lift_on_path: bool


def summarize_counter(counter: Counter) -> str:
    if not counter:
        return "(empty)"
    return ", ".join(f"{key}:{counter[key]}" for key in sorted(counter))


def config_to_list(cfg: Config) -> List[int]:
    return list(cfg)


def good_lifts(big: TpBadGraph, small_cfg: Config, k: int) -> List[Config]:
    lifts: List[Config] = []
    for x in range(3):
        lifted = insert_value(small_cfg, k, x)
        if lifted in big.good_cycle:
            lifts.append(lifted)
    return lifts


def canonical_path_to_phi(small: TpBadGraph, src: Config, k: int) -> Tuple[List[Config], List[int]]:
    """Choose a deterministic path to a Phi-achiever.

    Primary objective: minimize seam-step count.
    Secondary objective: minimize total path length.
    Tie-breaker: smaller node id first via heap order.
    """
    if src in small.good_cycle:
        return [src], []

    seam = {k - 1, k}
    start = small.bad_id[src]
    target_fc = small.phi_of(src)

    best: Dict[int, Tuple[int, int]] = {start: (0, 0)}
    parent: Dict[int, Tuple[Optional[int], Optional[int]]] = {start: (None, None)}
    heap: List[Tuple[int, int, int]] = [(0, 0, start)]
    target: Optional[int] = None

    while heap:
        seam_cost, path_len, node = heapq.heappop(heap)
        if (seam_cost, path_len) != best[node]:
            continue
        cfg = small.bad_configs[node]
        if small.fc_all[cfg] == target_fc:
            target = node
            break
        for nxt, mover in small.out_edges[node]:
            nxt_cost = seam_cost + (1 if mover in seam else 0)
            nxt_len = path_len + 1
            cand = (nxt_cost, nxt_len)
            prev = best.get(nxt)
            if prev is None or cand < prev:
                best[nxt] = cand
                parent[nxt] = (node, mover)
                heapq.heappush(heap, (nxt_cost, nxt_len, nxt))

    if target is None:
        raise RuntimeError(f"no path to Phi-achiever from {src}")

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
    return [small.bad_configs[node] for node in node_ids], movers


def first_point_above(
    big: TpBadGraph,
    nodes: List[Config],
    fcs: List[int],
    threshold: int,
    k: int,
) -> WitnessPoint:
    for idx, (cfg, fc_val) in enumerate(zip(nodes, fcs)):
        if fc_val > threshold:
            lifts = good_lifts(big, cfg, k)
            return WitnessPoint(index=idx, cfg=cfg, fc=fc_val, good_lifts=lifts)
    raise RuntimeError(f"path never exceeds threshold {threshold}")


def analyze_positive_residuals(n: int, k: int) -> Tuple[TpBadGraph, TpBadGraph, List[ResidualRecord]]:
    big = TpBadGraph(n)
    small = TpBadGraph(n - 1)
    big.ensure_scc()
    small.ensure_scc()
    offsite = offsite_summary(small, k)

    records: List[ResidualRecord] = []
    for c in big.all_configs:
        deleted = delete_config(c, k)
        fc_big = big.fc_all[c]
        phi_big = big.phi_of(c)
        g_big = phi_big - fc_big
        fc_small = small.fc_all[deleted]
        phi_small = small.phi_of(deleted)
        phi_off = offsite.phi_off[deleted]
        r_small = phi_small - fc_small
        r_off = phi_off - fc_small
        residual = r_small - g_big
        defect = fc_big - fc_small
        seam_bonus = phi_small - phi_off
        if residual <= 0:
            continue

        path_nodes, path_movers = canonical_path_to_phi(small, deleted, k)
        path_fcs = [small.fc_all[node] for node in path_nodes]
        first_offsite = first_point_above(big, path_nodes, path_fcs, phi_off, k)
        first_residual = first_point_above(big, path_nodes, path_fcs, fc_small + g_big, k)
        achiever = path_nodes[-1]

        records.append(
            ResidualRecord(
                c=c,
                deleted=deleted,
                fc_big=fc_big,
                phi_big=phi_big,
                g_big=g_big,
                fc_small=fc_small,
                phi_small=phi_small,
                phi_off=phi_off,
                r_small=r_small,
                r_off=r_off,
                residual=residual,
                seam_bonus=seam_bonus,
                defect=defect,
                path_nodes=path_nodes,
                path_movers=path_movers,
                path_fcs=path_fcs,
                path_seam_moves=sum(1 for mover in path_movers if mover in (k - 1, k)),
                first_offsite_excess=first_offsite,
                first_residual_excess=first_residual,
                achiever_good_lifts=good_lifts(big, achiever, k),
                any_good_lift_on_path=any(bool(good_lifts(big, node, k)) for node in path_nodes),
            )
        )

    return big, small, records


def check_deleted_from_cycle(big: TpBadGraph, small: TpBadGraph, k: int) -> List[Config]:
    return [cfg for cfg in sorted(big.good_cycle) if delete_config(cfg, k) not in small.good_cycle]


def check_simple_bound(big: TpBadGraph, small: TpBadGraph, k: int) -> Tuple[List[Tuple[Config, int]], Counter[int]]:
    violations: List[Tuple[Config, int]] = []
    gap_counter: Counter[int] = Counter()
    for c in big.all_configs:
        gap = small.phi_of(delete_config(c, k)) - big.fc_all[c]
        if gap > 0:
            violations.append((c, gap))
            gap_counter[gap] += 1
    return violations, gap_counter


def print_summary(big: TpBadGraph, small: TpBadGraph, k: int, records: List[ResidualRecord], max_examples: int) -> None:
    defect_residual = Counter((rec.defect, rec.residual) for rec in records)
    seam_bonus = Counter(rec.seam_bonus for rec in records)
    seam_move_count = Counter(rec.path_seam_moves for rec in records)
    mover_words = Counter(tuple(rec.path_movers) for rec in records)
    unique_deleted = {rec.deleted for rec in records}

    first_offsite_good = sum(rec.first_offsite_excess.has_good_lift for rec in records)
    first_residual_good = sum(rec.first_residual_excess.has_good_lift for rec in records)
    achiever_good = sum(bool(rec.achiever_good_lifts) for rec in records)
    any_path_good = sum(rec.any_good_lift_on_path for rec in records)

    deleted_from_cycle = check_deleted_from_cycle(big, small, k)
    simple_violations, simple_gap_counter = check_simple_bound(big, small, k)

    print(f"Residual-bound analysis for n={big.n}, k={k}")
    print(f"  size-{big.n} configs: {len(big.all_configs)}")
    print(f"  size-{big.n} good cycle: {len(big.good_cycle)}")
    print(f"  size-{small.n} configs: {len(small.all_configs)}")
    print(f"  size-{small.n} good cycle: {len(small.good_cycle)}")
    print()

    print("Positive residual sources")
    print(f"  count: {len(records)}")
    print(f"  unique deleted sources: {len(unique_deleted)}")
    print(f"  by (defect, residual): {defect_residual}")
    print(f"  seam bonus Phi-Phi_off on these sources: {summarize_counter(seam_bonus)}")
    print(f"  seam moves on canonical Phi path: {summarize_counter(seam_move_count)}")
    print(f"  top mover words: {', '.join(f'{list(word)}:{count}' for word, count in mover_words.most_common(8))}")
    print()

    print("Good-cycle-lift hypothesis checks")
    print(
        "  first config above Phi_off with a size-9 good-cycle lift: "
        f"{first_offsite_good} / {len(records)}"
    )
    print(
        "  first config above fc(delete(c)) + g_n(c) with a size-9 good-cycle lift: "
        f"{first_residual_good} / {len(records)}"
    )
    print(f"  final Phi-achievers with a size-9 good-cycle lift: {achiever_good} / {len(records)}")
    print(f"  any node on canonical witness path with a size-9 good-cycle lift: {any_path_good} / {len(records)}")
    print(
        "  size-9 good-cycle configs whose deletion is not size-8 good-cycle: "
        f"{len(deleted_from_cycle)} / {len(big.good_cycle)}"
    )
    print()

    print("Stronger bound check")
    print(f"  PhiFull(delete(c)) <= fc(c) violations: {len(simple_violations)} / {len(big.all_configs)}")
    print(f"  positive gaps PhiFull(delete(c)) - fc(c): {summarize_counter(simple_gap_counter)}")
    print()

    print("Sample traces")
    for idx, rec in enumerate(records[:max_examples], start=1):
        print(
            f"  [{idx}] c={format_cfg(rec.c)} delete(c)={format_cfg(rec.deleted)} "
            f"defect={rec.defect} residual={rec.residual}"
        )
        print(
            f"      fc_big={rec.fc_big} phi_big={rec.phi_big} g_big={rec.g_big} "
            f"fc_small={rec.fc_small} phi_small={rec.phi_small} phi_off={rec.phi_off}"
        )
        print(f"      movers={rec.path_movers}")
        print(f"      path_fc={rec.path_fcs}")
        print(
            f"      first above Phi_off: idx={rec.first_offsite_excess.index} "
            f"cfg={format_cfg(rec.first_offsite_excess.cfg)} "
            f"fc={rec.first_offsite_excess.fc} "
            f"good_lifts={len(rec.first_offsite_excess.good_lifts)}"
        )
        print(
            f"      first above fc(delete)+g: idx={rec.first_residual_excess.index} "
            f"cfg={format_cfg(rec.first_residual_excess.cfg)} "
            f"fc={rec.first_residual_excess.fc} "
            f"good_lifts={len(rec.first_residual_excess.good_lifts)}"
        )
    print()

    if deleted_from_cycle:
        print("Unexpected deleted-from-cycle examples:")
        for cfg in deleted_from_cycle[:5]:
            print(f"  {format_cfg(cfg)} -> {format_cfg(delete_config(cfg, k))}")
        print()

    if simple_violations:
        print("Sample stronger-bound violations")
        for idx, (cfg, gap) in enumerate(simple_violations[:5], start=1):
            print(
                f"  [{idx}] c={format_cfg(cfg)} fc(c)={big.fc_all[cfg]} "
                f"Phi(delete(c))={small.phi_of(delete_config(cfg, k))} gap={gap}"
            )
        print()


def maybe_dump_json(path: Optional[str], records: List[ResidualRecord]) -> None:
    if path is None:
        return

    def witness_to_json(w: WitnessPoint) -> Dict[str, object]:
        return {
            "index": w.index,
            "cfg": config_to_list(w.cfg),
            "fc": w.fc,
            "good_lifts": [config_to_list(cfg) for cfg in w.good_lifts],
        }

    payload = []
    for rec in records:
        item = asdict(rec)
        item["c"] = config_to_list(rec.c)
        item["deleted"] = config_to_list(rec.deleted)
        item["path_nodes"] = [config_to_list(cfg) for cfg in rec.path_nodes]
        item["achiever_good_lifts"] = [config_to_list(cfg) for cfg in rec.achiever_good_lifts]
        item["first_offsite_excess"] = witness_to_json(rec.first_offsite_excess)
        item["first_residual_excess"] = witness_to_json(rec.first_residual_excess)
        payload.append(item)

    with open(path, "w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2)


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=9, help="original size n")
    parser.add_argument("--k", type=int, default=4, help="deleted site k")
    parser.add_argument("--max-examples", type=int, default=8, help="sample traces to print")
    parser.add_argument("--dump-json", type=str, default=None, help="optional JSON output path for all positive-residual traces")
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)
    if args.n != 9 or args.k != 4:
        raise SystemExit("This script currently supports only the requested case n=9, k=4.")

    big, small, records = analyze_positive_residuals(args.n, args.k)
    print_summary(big, small, args.k, records, args.max_examples)
    maybe_dump_json(args.dump_json, records)
    if args.dump_json is not None:
        print(f"Wrote {len(records)} trace records to {args.dump_json}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
